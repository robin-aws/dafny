using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Xunit.Abstractions;

namespace XUnitExtensions.Lit {
  public class MainMethodLitCommand : ILitCommand {
    private readonly Assembly assembly;
    private readonly string[] arguments;
    private readonly Action<TextReader?, TextWriter?, TextWriter?> setStreamsAction;

    protected MainMethodLitCommand(Assembly assembly, string[] arguments, Action<TextReader?, TextWriter?, TextWriter?>? setStreamsAction) {
      this.assembly = assembly;
      this.arguments = arguments;
      if (setStreamsAction != null) {
        this.setStreamsAction = setStreamsAction;
      } else {
        this.setStreamsAction = (inputReader, outputWriter, errorWriter) => {
          if (inputReader != null) {
            Console.SetIn(inputReader);
          }

          if (outputWriter != null) {
            Console.SetOut(outputWriter);
          }

          if (errorWriter != null) {
            Console.SetError(errorWriter);
          }
        };
      }
    }

    public static ILitCommand Parse(Assembly assembly, IEnumerable<string> arguments, LitTestConfiguration config, 
        bool invokeDirectly, Action<TextReader?, TextWriter?, TextWriter?>? setStreamsAction = null) {
      var result = new MainMethodLitCommand(assembly, arguments.ToArray(), setStreamsAction);
      return invokeDirectly ? result : result.ToShellCommand(config);
    }

    public (int, string, string) Execute(ITestOutputHelper outputHelper, TextReader? inputReader, TextWriter? outputWriter, TextWriter? errorWriter) {
      setStreamsAction(inputReader, outputWriter, errorWriter);
      
      var exitCode = (int)assembly.EntryPoint!.Invoke(null, new object[] { arguments })!;

      Console.Out.Flush();
      Console.Error.Flush();
      
      return (exitCode, "", "");
    }

    public ILitCommand ToShellCommand(LitTestConfiguration config) {
      var shellArguments = new[] { assembly.Location }.Concat(arguments);
      return new ShellLitCommand(config, "dotnet", shellArguments, config.PassthroughEnvironmentVariables);
    }

    public override string ToString() {
      var builder = new StringBuilder();
      builder.Append(assembly.EntryPoint);
      builder.Append(' ');
      builder.AppendJoin(" ", arguments);
      return builder.ToString();
    }
  }
}