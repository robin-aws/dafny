using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.IO;

namespace Microsoft.Dafny.Compilers;

public class CppCompilerBackend : ExecutableBackend {

  protected override SinglePassCompiler CreateCompiler() {
    return new CppCompiler(Options, Reporter, OtherFileNames);
  }

  private string ComputeExeName(string targetFilename) {
    return Path.ChangeExtension(Path.GetFullPath(targetFilename), "exe");
  }

  public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText,
    string/*?*/ callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
    var assemblyLocation = System.Reflection.Assembly.GetExecutingAssembly().Location;
    Contract.Assert(assemblyLocation != null);
    var codebase = Path.GetDirectoryName(assemblyLocation);
    Contract.Assert(codebase != null);
    compilationResult = null;
    var psi = PrepareProcessStartInfo("g++", new List<string> {
      "-Wall",
      "-Wextra",
      "-Wpedantic",
      "-Wno-unused-variable",
      "-Wno-deprecated-copy",
      "-Wno-unused-label",
      "-Wno-unused-but-set-variable",
      "-Wno-unknown-warning-option",
      "-g",
      "-std=c++17",
      "-I", codebase,
      "-o", ComputeExeName(targetFilename),
      targetFilename
    });
    return 0 == RunProcess(psi, outputWriter, outputWriter, "Error while compiling C++ files.");
  }

  public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain /*?*/,
    string targetFilename, ReadOnlyCollection<string> otherFileNames,
    object compilationResult, TextWriter outputWriter, TextWriter errorWriter) {
    var psi = PrepareProcessStartInfo(ComputeExeName(targetFilename), Options.MainArgs);
    return 0 == RunProcess(psi, outputWriter, errorWriter);
  }

  public override Command GetCommand() {
    return new Command(TargetId, $@"Translate Dafny sources to {TargetName} source and build files.

This back-end has various limitations (see Docs/Compilation/Cpp.md).
This includes lack of support for BigIntegers (aka int), most higher order functions,
and advanced features like traits or co-inductive types.");
  }

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".h" };

  public override string TargetName => "C++";
  public override bool IsStable => true;
  public override string TargetExtension => "cpp";

  public override bool SupportsInMemoryCompilation => false;

  public override bool TextualTargetIsExecutable => false;

  public CppCompilerBackend(DafnyOptions options) : base(options) {
  }
}