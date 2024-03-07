using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny;

public abstract class ExecutableBackend : IExecutableBackend {
  // May be null for backends that don't use the single-pass compiler logic
  protected SinglePassCodeGenerator codeGenerator;

  protected ExecutableBackend(DafnyOptions options) : base(options) {
  }

  public override IReadOnlySet<Feature> UnsupportedFeatures => CreateCodeGenerator().UnsupportedFeatures;

  public override bool SupportsDatatypeWrapperErasure =>
    CreateCodeGenerator()?.SupportsDatatypeWrapperErasure ?? base.SupportsDatatypeWrapperErasure;

  public override string ModuleSeparator => CodeGenerator.ModuleSeparator;

  public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
    CheckInstantiationReplaceableModules(dafnyProgram);
    ProcessOuterModules(dafnyProgram);
    CodeGenerator.Compile(dafnyProgram, output);
  }

  protected void CheckInstantiationReplaceableModules(Program dafnyProgram) {
    foreach (var compiledModule in dafnyProgram.Modules()) {
      if (compiledModule.Implements is { Kind: ImplementationKind.Replacement }) {
        if (compiledModule.IsExtern(Options, out _, out var name) && name != null) {
          Reporter!.Error(MessageSource.Compiler, compiledModule.Tok,
            "inside a module that replaces another, {:extern} attributes may only be used without arguments");
        }
      }

      if (compiledModule.ModuleKind == ModuleKindEnum.Replaceable && compiledModule.Replacement == null) {
        if (compiledModule.ShouldCompile(dafnyProgram.Compilation)) {
          Reporter!.Error(MessageSource.Compiler, compiledModule.Tok,
            $"when producing executable code, replaceable modules must be replaced somewhere in the program. For example, `module {compiledModule.Name}Impl replaces {compiledModule.Name} {{ ... }}`");
        }
      }
    }
  }

  protected void ProcessOuterModules(Program dafnyProgram) {
    var outerModules = GetOuterModules();
    ModuleDefinition rootUserModule = null;
    foreach (var outerModule in outerModules) {
      var newRoot = new ModuleDefinition(RangeToken.NoToken, new Name(outerModule), new List<IToken>(),
        ModuleKindEnum.Concrete, false,
        null, null, null);
      newRoot.EnclosingModule = rootUserModule;
      rootUserModule = newRoot;
    }

    if (rootUserModule != null) {
      dafnyProgram.DefaultModuleDef.NameNode = rootUserModule.NameNode;
      dafnyProgram.DefaultModuleDef.EnclosingModule = rootUserModule.EnclosingModule;
    }

    foreach (var module in dafnyProgram.CompileModules) {
      module.ClearNameCache();
    }
  }

  public override void OnPreCompile(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames) {
    base.OnPreCompile(reporter, otherFileNames);
    codeGenerator = CreateCodeGenerator();
  }

  SinglePassCodeGenerator CodeGenerator {
    get {
      if (codeGenerator == null) {
        codeGenerator = CreateCodeGenerator();
      }

      return codeGenerator;
    }
  }

  public override Task<bool> OnPostGenerate(string dafnyProgramName, string targetDirectory, TextWriter outputWriter) {
    CodeGenerator.Coverage.WriteLegendFile();
    return Task.FromResult(true);
  }

  protected abstract SinglePassCodeGenerator CreateCodeGenerator();

  public override string PublicIdProtect(string name) {
    return CodeGenerator.PublicIdProtect(name);
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    CodeGenerator.EmitCallToMain(mainMethod, baseName, callToMainTree);
  }

  public ProcessStartInfo PrepareProcessStartInfo(string programName, IEnumerable<string> args = null) {
    var psi = new ProcessStartInfo(programName) {
      UseShellExecute = false,
      CreateNoWindow = false, // https://github.com/dotnet/runtime/issues/68259
      RedirectStandardOutput = true,
    };
    foreach (var arg in args ?? Enumerable.Empty<string>()) {
      psi.ArgumentList.Add(arg);
    }
    return psi;
  }

  public Task<int> RunProcess(ProcessStartInfo psi,
    TextWriter outputWriter,
    TextWriter errorWriter,
    string errorMessage = null) {
    return StartProcess(psi, outputWriter) is { } process ?
      WaitForExit(process, outputWriter, errorWriter, errorMessage) : Task.FromResult(-1);
  }

  public async Task<int> WaitForExit(Process process, TextWriter outputWriter, TextWriter errorWriter, string errorMessage = null) {

    await PassthroughBuffer(process.StandardError, errorWriter);
    await PassthroughBuffer(process.StandardOutput, outputWriter);
    await process.WaitForExitAsync();
    if (process.ExitCode != 0 && errorMessage != null) {
      await outputWriter.WriteLineAsync($"{errorMessage} Process exited with exit code {process.ExitCode}");
    }

    return process.ExitCode;
  }


  protected static async Task PassthroughBuffer(TextReader input, TextWriter output) {
    char[] buffer = new char[256];
    int readCount;
    while ((readCount = await input.ReadBlockAsync(buffer)) > 0) {
      await output.WriteAsync(buffer, 0, readCount);
    }
  }

  public Process StartProcess(ProcessStartInfo psi, TextWriter outputWriter) {
    string additionalInfo = "";

    try {
      psi.RedirectStandardError = true;
      if (Process.Start(psi) is { } process) {
        return process;
      }
    } catch (System.ComponentModel.Win32Exception e) {
      additionalInfo = $": {e.Message}";
    }

    outputWriter.WriteLine($"Error: Unable to start {psi.FileName}{additionalInfo}");
    return null;
  }

  public override Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText,
    string callToMain /*?*/, string targetFilename, /*?*/
    ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, TextWriter outputWriter) {
    Contract.Requires(dafnyProgramName != null);
    Contract.Requires(targetProgramText != null);
    Contract.Requires(otherFileNames != null);
    Contract.Requires(otherFileNames.Count == 0 || targetFilename != null);
    Contract.Requires(this.SupportsInMemoryCompilation || targetFilename != null);
    Contract.Requires(!runAfterCompile || callToMain != null);
    Contract.Requires(outputWriter != null);

    return Task.FromResult((true, (object)null));
  }

  public override Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText,
    string callToMain, /*?*/
    string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    object compilationResult, TextWriter outputWriter, TextWriter errorWriter) {
    Contract.Requires(dafnyProgramName != null);
    Contract.Requires(targetProgramText != null);
    Contract.Requires(otherFileNames != null);
    Contract.Requires(otherFileNames.Count == 0 || targetFilename != null);
    Contract.Requires(outputWriter != null);
    return Task.FromResult(true);
  }

  public override void InstrumentCompiler(CompilerInstrumenter instrumenter, Program dafnyProgram) {
    if (CodeGenerator == null) {
      return;
    }

    instrumenter.Instrument(this, CodeGenerator, dafnyProgram);
  }

  protected static void WriteFromFile(string inputFilename, TextWriter outputWriter) {
    var rd = new StreamReader(new FileStream(inputFilename, FileMode.Open, FileAccess.Read));
    SinglePassCodeGenerator.WriteFromStream(rd, outputWriter);
  }

  protected async Task<bool> RunTargetDafnyProgram(string targetFilename, TextWriter outputWriter, TextWriter errorWriter, bool verify) {

    /*
     * In order to work for the continuous integration, we need to call the Dafny compiler using dotnet
     * because dafny is not currently in the path
     */

    var where = System.Reflection.Assembly.GetExecutingAssembly().Location;
    where = Path.GetDirectoryName(where);
    var dafny = where + "/Dafny.dll";

    var opt = Options;
    var args = opt.MainArgs
      .Prepend(targetFilename);
    if (!verify) {
      args = args.Prepend("--no-verify");
    }
    args = args
      .Prepend("--target:cs")
      .Prepend("run")
      .Prepend(dafny);
    var psi = PrepareProcessStartInfo("dotnet", args);
    await Console.Out.WriteLineAsync(string.Join(", ", psi.ArgumentList));
    /*
     * When this code was written, the Dafny compiler cannot be made completely silent.
     * This is a problem for this specific compiler and the integration tests because the second
     * call to the compiler makes unexpected writes to the output.
     * The following code is catching the output from the second compiler call (the one that executes the code)
     * and stripping out the first two lines and the last line.
     */

    psi.RedirectStandardOutput = true;
    psi.RedirectStandardError = true;
    var process = new Process();
    process.StartInfo = psi;
    var outputBuilder = new List<string>();
    var errorBuilder = new List<string>();
    process.OutputDataReceived += (sender, args) => outputBuilder.Add(args.Data);
    process.ErrorDataReceived += (sender, args) => errorBuilder.Add(args.Data);

    try {
      process.Start();
      process.BeginOutputReadLine();
      process.BeginErrorReadLine();
      await process.WaitForExitAsync();
      process.CancelOutputRead();
      process.CancelErrorRead();

      for (int i = 2; i < outputBuilder.Count - 1; i++) {
        await outputWriter.WriteLineAsync(outputBuilder[i]);
      }

      for (int i = 0; i < errorBuilder.Count - 1; i++) {
        await errorWriter.WriteLineAsync(errorBuilder[i]);
      }

      if (process.ExitCode != 0) {
        await outputWriter.WriteLineAsync($"Process exited with exit code {process.ExitCode}");
        return false;
      }

    } catch (System.ComponentModel.Win32Exception e) {
      string additionalInfo = $": {e.Message}";
      await outputWriter.WriteLineAsync($"Error: Unable to start {psi.FileName}{additionalInfo}");
      return false;
    }

    return true;
  }
}
