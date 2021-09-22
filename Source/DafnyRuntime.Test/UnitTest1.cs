using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Threading.Tasks;
using Microsoft.Coyote;
using Microsoft.Coyote.Specifications;
using Microsoft.Coyote.SystematicTesting;
using Xunit;
using Xunit.Abstractions;

namespace DafnyRuntime.Test {
  
  
  public class ThreadSafety {
    
    ITestOutputHelper Output;

    public ThreadSafety(ITestOutputHelper output)
    {
      Output = output;
    }

    [Fact(Timeout = 5000)]
    public void RunCoyoteTest()
    {
      var config = Configuration.Create();
      TestingEngine engine = TestingEngine.Create(config, ConcatSequence);
      engine.Run();
      
      List<string> filenames = new List<string>(engine.TryEmitTraces(Directory.GetCurrentDirectory(), "ConcatSequence"));
      foreach (var item in filenames)
      {
        Output.WriteLine("See log file: {0}", item);
      }
      
      var report = engine.TestReport;
      Assert.True(report.NumOfFoundBugs == 0, $"Coyote found {report.NumOfFoundBugs} bug(s).");
    }
    
    [Fact]
    public void ReplayCoyoteTest() {
      var tracePath = "/Users/salkeldr/Documents/GitHub/dafny/Source/DafnyRuntime.Test/bin/Debug/net5.0/ConcatImmutableList_0.schedule";
      var trace = File.ReadAllText(tracePath);
      var config = Configuration.Create().WithReplayStrategy(trace);
      TestingEngine engine = TestingEngine.Create(config, ConcatImmutableList);
      engine.Run();
      
      var report = engine.TestReport;
      Assert.True(report.NumOfFoundBugs == 0, $"Coyote found {report.NumOfFoundBugs} bug(s).");
    }

    [Fact]
    public async Task ConcatSequence() {
      var hello = Dafny.Sequence<char>.FromString("Hello ");
      var world = Dafny.Sequence<char>.FromString("World!");
      var helloWorld = Dafny.Sequence<char>.Concat(hello, world);
      // var elements = helloWorld.Elements;
      var task1 = GetFirstElement(helloWorld);
      var task2 = GetFirstElement(helloWorld);
      var results = await Task.WhenAll(task1, task2);
      Assert.Equal('H', results[0]);
      Assert.Equal('H', results[1]);
    }

    public Task<T> GetFirstElement<T>(Dafny.ISequence<T> sequence) {
      return Task.Run(() => {
        return sequence.Select(0);
      });
    }
    
    [Fact]
    public async Task ConcatImmutableList() {
      var hello = ImmutableList.CreateRange("Hello ");
      var world = ImmutableList.CreateRange("World!");
      var helloWorld = hello.AddRange(world);
      var task1 = GetFirstElement(helloWorld);
      var task2 = GetFirstElement(helloWorld);
      await Task.WhenAll(task1, task2);
    }
    
    public Task<T> GetFirstElement<T>(ImmutableList<T> list) {
      return Task.Run(() => {
        return list[0];
      });
    }
  }
}