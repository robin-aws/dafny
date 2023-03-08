using System.Reflection;
using System.Text;
using System.Text.RegularExpressions;
using CommandLine;
using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;
using Nerdbank.Streams;
using XUnitExtensions;
using XUnitExtensions.Lit;

namespace TestDafny; 

[Verb("for-each-compiler", HelpText = "Execute the given test file for every compiler, and assert the output matches the <test file>.expect file.")]
public class ForEachCompilerOptions {

  [Value(0, Required = true, MetaName = "Test file", HelpText = "The *.dfy file to test.")]
  public string? TestFile { get; set; } = null;

  [Option("dafny", HelpText = "The dafny CLI to test with. Defaults to the locally built DafnyDriver project.")]
  public string? DafnyCliPath { get; set; } = null;

  [Value(1, MetaName = "Dafny CLI arguments", HelpText = "Any arguments following '--' will be passed to the dafny CLI unaltered.")] public IEnumerable<string> OtherArgs { get; set; } = Array.Empty<string>();
}

[Verb("features", HelpText = "Print the Markdown content documenting feature support for each compiler.")]
public class FeaturesOptions {
  [Value(1)] public IEnumerable<string> OtherArgs { get; set; } = Array.Empty<string>();
}

public class TestDafny {

  private static readonly Assembly DafnyAssembly = typeof(Dafny.Dafny).Assembly;

  public static int Main(string[] args) {
    var result = -1;
    var parser = new CommandLine.Parser(with => {
      with.EnableDashDash = true;
      with.HelpWriter = Console.Error;
    });
    var parseResult = parser.ParseArguments<ForEachCompilerOptions, FeaturesOptions>(args);
    parseResult.WithParsed<ForEachCompilerOptions>(options => {
      result = ForEachCompilerInProcess(options).Result;
    }).WithParsed<FeaturesOptions>(options => {
      result = GenerateCompilerTargetSupportTable(options);
    });

    return result;
  }

  private static DafnyOptions? ParseDafnyOptions(IEnumerable<string> dafnyArgs) {
    var dafnyOptions = new DafnyOptions();
    var success = dafnyOptions.Parse(dafnyArgs.ToArray());
    return success ? dafnyOptions : null;
  }

  private static async Task<int> ForEachCompilerInProcess(ForEachCompilerOptions options) {
    var dafnyOptions = ParseDafnyOptions(options.OtherArgs);
    if (dafnyOptions == null) {
      return (int)DafnyDriver.CommandLineArgumentsResult.PREPROCESSING_ERROR;
    }
    DafnyOptions.Install(dafnyOptions);
    var driver = new DafnyDriver(dafnyOptions);

    var localOut = new StringWriter();
    var actualOut = Console.Out;
    Console.SetOut(localOut);
    var localError = new StringWriter();
    var actualError = Console.Error;
    Console.SetError(localError);
    
    // First verify the file (and assume that verification should be successful).
    // Older versions of test files that now use %testDafnyForEachCompiler were sensitive to the number
    // of verification conditions (i.e. the X in "Dafny program verifier finished with X verified, 0 errors"),
    // but this was never meaningful and only added maintenance burden.
    // Here we only ensure that verification is successful.

    actualOut.WriteLine("Parsing and resolving...");
    var reporter = new ConsoleErrorReporter();
    var dafnyFile = new DafnyFile(options.TestFile);
    var err = Microsoft.Dafny.Main.ParseCheck(Util.List(dafnyFile), dafnyFile.FilePath, reporter, out var dafnyProgram);
    if (err != null) {
      actualOut.Write(localOut);
      actualOut.WriteLine(err);
      return -1;
    }

    Console.Out.WriteLine("Verifying...");
    var boogiePrograms = DafnyDriver.Translate(dafnyOptions, dafnyProgram).ToList();
    var baseName = dafnyFile.FilePath;
    var (verified, outcome, moduleStats) = await driver.BoogieAsync(baseName, boogiePrograms, dafnyFile.FilePath);
    
    // Then execute the program for each available compiler.
    // Note we DON'T first check if the program verified above
    // because that's also what DafnyDriver.ProcessFilesAsync does:
    // it relies on Compile() to check that (and possibly compile even if verification failed or didn't run
    // based on ForceCompile or SpillTargetCode). 
    
    var expectFile = options.TestFile + ".expect";
    var expectedOutput = File.ReadAllText(expectFile);

    var success = true;
    foreach (var plugin in dafnyOptions.Plugins) {
      foreach (var compiler in plugin.GetCompilers()) {
        actualOut.WriteLine($"Executing on {compiler.TargetLanguage}...");
        
        // Reset the local stdout buffer so we can just capture the execution output.
        localOut = new StringWriter();
        Console.SetOut(localOut);
        localError = new StringWriter();
        Console.SetError(localError);
        
        dafnyOptions.Backend = compiler;
        
        bool compiled;
        try {
          compiled = DafnyDriver.Compile(dafnyFile.FilePath, Util.List<string>().AsReadOnly(), dafnyProgram, outcome, moduleStats, verified);
        } catch (UnsupportedFeatureException e) {
          if (!DafnyOptions.O.Backend.UnsupportedFeatures.Contains(e.Feature)) {
            throw new Exception($"'{e.Feature}' is not an element of the {DafnyOptions.O.Backend.TargetId} compiler's UnsupportedFeatures set");
          }
          reporter.Error(MessageSource.Compiler, e.Token, e.Message);
          compiled = false;
        }
        
        var output = localOut.ToString();
        var error = localError.ToString();

        if (!compiled) {
          if (error == "" && OnlyUnsupportedFeaturesErrors(compiler, output)) {
            // All good!
          } else {
            actualOut.WriteLine("Execution failed, for reasons other than known unsupported features. Output:");
            actualOut.WriteLine(output);
            actualOut.WriteLine("Error:");
            actualOut.WriteLine(error);
          }
        } else {
          var diffMessage = AssertWithDiff.GetDiffMessage(expectedOutput, output);
          if (diffMessage != null) {
            actualOut.WriteLine(diffMessage);
            success = false;
          }
        }
      }
    }

    if (success) {
      Console.Out.WriteLine(
        $"All executions were successful and matched the expected output (or reported errors for known unsupported features)!");
      return 0;
    } else {
      return -1;
    }
  }

  private static (int, string, string) RunDafny(string? dafnyCLIPath, IEnumerable<string> arguments) {
    var argumentsWithDefaults = arguments.Concat(DafnyDriver.DefaultArgumentsForTesting);
    ILitCommand command;
    if (dafnyCLIPath != null) {
      command = new ShellLitCommand(dafnyCLIPath, argumentsWithDefaults, DafnyDriver.ReferencedEnvironmentVariables);
    } else {
      var dotnetArguments = new[] { DafnyAssembly.Location }.Concat(argumentsWithDefaults);
      command = new ShellLitCommand("dotnet", dotnetArguments, DafnyDriver.ReferencedEnvironmentVariables);
    }
    return command.Execute(null, null, null, null);
  }

  private static bool OnlyUnsupportedFeaturesErrors(IExecutableBackend backend, string output) {
    using (StringReader sr = new StringReader(output)) {
      string? line;
      while ((line = sr.ReadLine()) != null) {
        if (!IsAllowedOutputLine(backend, line)) {
          return false;
        }
      }
    }

    return true;
  }

  private static bool IsAllowedOutputLine(IExecutableBackend backend, string line) {
    line = line.Trim();
    if (line.Length == 0) {
      return true;
    }

    // This is the first non-blank line we expect when we pass /noVerify
    if (line == "Dafny program verifier did not attempt verification") {
      return true;
    }

    // This is output if the compiler emits any errors
    if (line.StartsWith("Wrote textual form of partial target program to")) {
      return true;
    }

    // This is output if included files have errors,
    // which is expected if we're including another test file and testing different CLI options
    if (Regex.IsMatch(line, "Error: the included file .* contains error\\(s\\)")) {
      return true;
    }

    var prefixIndex = line.IndexOf(UnsupportedFeatureException.MessagePrefix, StringComparison.Ordinal);
    if (prefixIndex < 0) {
      return false;
    }

    var featureDescription = line[(prefixIndex + UnsupportedFeatureException.MessagePrefix.Length)..];
    var feature = FeatureDescriptionAttribute.ForDescription(featureDescription);
    if (backend.UnsupportedFeatures.Contains(feature)) {
      return true;
    }

    // This is an internal inconsistency error
    throw new Exception(
      $"Compiler rejected feature '{feature}', which is not an element of its UnsupportedFeatures set");
  }

  private static int GenerateCompilerTargetSupportTable(FeaturesOptions featuresOptions) {
    var dafnyOptions = ParseDafnyOptions(featuresOptions.OtherArgs);
    if (dafnyOptions == null) {
      return (int)DafnyDriver.CommandLineArgumentsResult.PREPROCESSING_ERROR;
    }

    // Header
    Console.Out.Write("| Feature |");
    var allCompilers = dafnyOptions.Plugins.SelectMany(p => p.GetCompilers()).ToList();
    foreach (var compiler in allCompilers) {
      Console.Out.Write($" {compiler.TargetLanguage} |");
    }

    Console.Out.WriteLine();

    // Horizontal rule ("|----|---|...")
    Console.Out.Write("|-|");
    foreach (var _ in allCompilers) {
      Console.Out.Write($"-|");
    }

    Console.Out.WriteLine();

    var footnotes = new StringBuilder();
    foreach (var feature in Enum.GetValues(typeof(Feature)).Cast<Feature>()) {
      var description = FeatureDescriptionAttribute.GetDescription(feature);
      var footnoteLink = "";
      if (description.FootnoteIdentifier != null) {
        footnoteLink = $"[^{description.FootnoteIdentifier}]";
        footnotes.AppendLine($"{footnoteLink}: {description.Footnote}");
        footnotes.AppendLine();
      }

      Console.Out.Write($"| [{description.Description}](#{description.ReferenceManualSection}){footnoteLink} |");
      foreach (var compiler in allCompilers) {
        var supported = !compiler.UnsupportedFeatures.Contains(feature);
        var cell = supported ? " X " : "";
        Console.Out.Write($" {cell} |");
      }

      Console.Out.WriteLine();
    }

    Console.Out.WriteLine();
    Console.Out.WriteLine(footnotes);

    return 0;
  }
}