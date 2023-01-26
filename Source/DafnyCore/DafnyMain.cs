//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.IO;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace Microsoft.Dafny {

  public class IllegalDafnyFile : Exception { }

  public class DafnyFile {
    public bool UseStdin { get; private set; }
    public string FilePath { get; private set; }
    public string CanonicalPath { get; private set; }
    public string BaseName { get; private set; }
    public bool IsPrecompiled { get; set; }
    public string SourceFileName { get; private set; }

    // Returns a canonical string for the given file path, namely one which is the same
    // for all paths to a given file and different otherwise. The best we can do is to
    // make the path absolute -- detecting case and canonicalizing symbolic and hard
    // links are difficult across file systems (which may mount parts of other filesystems,
    // with different characteristics) and is not supported by .Net libraries
    public static string Canonicalize(String filePath) {
      return Path.GetFullPath(filePath);
    }
    public static List<string> FileNames(IList<DafnyFile> dafnyFiles) {
      var sourceFiles = new List<string>();
      foreach (DafnyFile f in dafnyFiles) {
        sourceFiles.Add(f.FilePath);
      }
      return sourceFiles;
    }
    public DafnyFile(string filePath, bool useStdin = false) {
      UseStdin = useStdin;
      FilePath = filePath;
      BaseName = Path.GetFileName(filePath);

      var extension = useStdin ? ".dfy" : Path.GetExtension(filePath);
      if (extension != null) { extension = extension.ToLower(); }

      // Normalizing symbolic links appears to be not
      // supported in .Net APIs, because it is very difficult in general
      // So we will just use the absolute path, lowercased for all file systems.
      // cf. IncludeComparer.CompareTo
      CanonicalPath = Canonicalize(filePath);

      if (!useStdin && !Path.IsPathRooted(filePath)) {
        filePath = Path.GetFullPath(filePath);
      }

      if (extension == ".dfy" || extension == ".dfyi") {
        IsPrecompiled = false;
        SourceFileName = filePath;
      } else if (extension == ".dll") {
        IsPrecompiled = true;

        var sourceText = GetDafnySourceAttributeText(filePath);
        if (sourceText == null) { throw new IllegalDafnyFile(); }
        SourceFileName = Path.GetTempFileName();
        File.WriteAllText(SourceFileName, sourceText);

      } else {
        throw new IllegalDafnyFile();
      }
    }

    private static string GetDafnySourceAttributeText(string dllPath) {
      if (!File.Exists(dllPath)) {
        throw new IllegalDafnyFile();
      }
      using var dllFs = new FileStream(dllPath, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);
      using var dllPeReader = new PEReader(dllFs);
      var dllMetadataReader = dllPeReader.GetMetadataReader();

      foreach (var attrHandle in dllMetadataReader.CustomAttributes) {
        var attr = dllMetadataReader.GetCustomAttribute(attrHandle);
        try {
          var constructor = dllMetadataReader.GetMemberReference((MemberReferenceHandle)attr.Constructor);
          var attrType = dllMetadataReader.GetTypeReference((TypeReferenceHandle)constructor.Parent);
          if (dllMetadataReader.GetString(attrType.Name) == "DafnySourceAttribute") {
            var decoded = attr.DecodeValue(new StringOnlyCustomAttributeTypeProvider());
            return (string)decoded.FixedArguments[0].Value;
          }
        } catch (InvalidCastException) {
          // Ignore - the Handle casts are handled as custom explicit operators,
          // and there's no way I can see to test if the cases will succeed ahead of time.
        }
      }

      return null;
    }

    // Dummy implementation of ICustomAttributeTypeProvider, providing just enough
    // functionality to successfully decode a DafnySourceAttribute value.
    private class StringOnlyCustomAttributeTypeProvider : ICustomAttributeTypeProvider<System.Type> {
      public System.Type GetPrimitiveType(PrimitiveTypeCode typeCode) {
        if (typeCode == PrimitiveTypeCode.String) {
          return typeof(string);
        }
        throw new NotImplementedException();
      }

      public System.Type GetTypeFromDefinition(MetadataReader reader, TypeDefinitionHandle handle, byte rawTypeKind) {
        throw new NotImplementedException();
      }

      public System.Type GetTypeFromReference(MetadataReader reader, TypeReferenceHandle handle, byte rawTypeKind) {
        throw new NotImplementedException();
      }

      public System.Type GetSZArrayType(System.Type elementType) {
        throw new NotImplementedException();
      }

      public System.Type GetSystemType() {
        throw new NotImplementedException();
      }

      public System.Type GetTypeFromSerializedName(string name) {
        throw new NotImplementedException();
      }

      public PrimitiveTypeCode GetUnderlyingEnumType(System.Type type) {
        throw new NotImplementedException();
      }

      public bool IsSystemType(System.Type type) {
        throw new NotImplementedException();
      }
    }
  }

  public class Main {

    public static void MaybePrintProgram(Program program, string filename, bool afterResolver) {
      if (filename == null) {
        return;
      }

      var tw = filename == "-" ? Console.Out : new StreamWriter(filename);
      var pr = new Printer(tw, DafnyOptions.O.PrintMode);
      pr.PrintProgram(program, afterResolver);
    }

    /// <summary>
    /// Returns null on success, or an error string otherwise.
    /// </summary>
    public static string ParseCheck(IList<DafnyFile/*!*/>/*!*/ files, string/*!*/ programName, ErrorReporter reporter, out Program program)
    //modifies Bpl.DafnyOptions.O.XmlSink.*;
    {
      string err = Parse(files, programName, reporter, out program);
      if (err != null) {
        return err;
      }

      return Resolve(program, reporter);
    }

    public static string Parse(IList<DafnyFile> files, string programName, ErrorReporter reporter, out Program program) {
      Contract.Requires(programName != null);
      Contract.Requires(files != null);
      program = null;
      ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
      BuiltIns builtIns = new BuiltIns();

      foreach (DafnyFile dafnyFile in files) {
        Contract.Assert(dafnyFile != null);
        if (DafnyOptions.O.XmlSink is { IsOpen: true } && !dafnyFile.UseStdin) {
          DafnyOptions.O.XmlSink.WriteFileFragment(dafnyFile.FilePath);
        }
        if (DafnyOptions.O.Trace) {
          Console.WriteLine("Parsing " + dafnyFile.FilePath);
        }

        var include = dafnyFile.IsPrecompiled ? new Include(Token.NoToken, null, dafnyFile.SourceFileName, false) : null;
        var err = ParseFile(dafnyFile, include, module, builtIns, new Errors(reporter), !dafnyFile.IsPrecompiled, !dafnyFile.IsPrecompiled);
        if (err != null) {
          return err;
        }
      }

      if (!(DafnyOptions.O.DisallowIncludes || DafnyOptions.O.PrintIncludesMode == DafnyOptions.IncludesModes.Immediate)) {
        string errString = ParseIncludesDepthFirstNotCompiledFirst(module, builtIns, files.Select(f => f.CanonicalPath).ToHashSet(), new Errors(reporter));
        if (errString != null) {
          return errString;
        }
      }

      if (DafnyOptions.O.PrintIncludesMode == DafnyOptions.IncludesModes.Immediate) {
        DependencyMap dmap = new DependencyMap();
        dmap.AddIncludes(((LiteralModuleDecl)module).ModuleDef.Includes);
        dmap.PrintMap();
      }

      program = new Program(programName, module, builtIns, reporter);

      MaybePrintProgram(program, DafnyOptions.O.DafnyPrintFile, false);

      return null; // success
    }

    public static string Resolve(Program program, ErrorReporter reporter) {
      if (DafnyOptions.O.NoResolve || DafnyOptions.O.NoTypecheck) { return null; }

      Dafny.Resolver r = new Dafny.Resolver(program);
      r.ResolveProgram(program);
      MaybePrintProgram(program, DafnyOptions.O.DafnyPrintResolvedFile, true);

      if (reporter.ErrorCountUntilResolver != 0) {
        return string.Format("{0} resolution/type errors detected in {1}", reporter.Count(ErrorLevel.Error), program.Name);
      }

      return null;  // success
    }

    // Lower-case file names before comparing them, since Windows uses case-insensitive file names
    private class IncludeComparer : IComparer<Include> {
      public int Compare(Include x, Include y) {
        return x.CompareTo(y);
      }
    }

    public static string ParseIncludesDepthFirstNotCompiledFirst(ModuleDecl module, BuiltIns builtIns, ISet<string> excludeFiles, Errors errs) {
      var includesFound = new SortedSet<Include>(new IncludeComparer());
      var allIncludes = ((LiteralModuleDecl)module).ModuleDef.Includes;
      var notCompiledRoots = allIncludes.Where(include => !include.CompileIncludedCode).ToList();
      var compiledRoots = allIncludes.Where(include => include.CompileIncludedCode).ToList();
      allIncludes.Clear();
      allIncludes.AddRange(notCompiledRoots);

      var notCompiledResult = TraverseIncludesFrom(0);
      if (notCompiledResult != null) {
        return notCompiledResult;
      }

      var notCompiledIncludeCount = allIncludes.Count;
      allIncludes.AddRange(compiledRoots);

      var compiledResult = TraverseIncludesFrom(notCompiledIncludeCount);
      if (compiledResult != null) {
        return compiledResult;
      }

      if (DafnyOptions.O.PrintIncludesMode != DafnyOptions.IncludesModes.None) {
        var dependencyMap = new DependencyMap();
        dependencyMap.AddIncludes(allIncludes);
        dependencyMap.PrintMap();
      }

      return null; // Success

      string TraverseIncludesFrom(int startingIndex) {
        var includeIndex = startingIndex;
        var stack = new Stack<Include>();

        while (true) {
          var addedItems = allIncludes.Skip(includeIndex);
          foreach (var addedItem in addedItems.Reverse()) {
            stack.Push(addedItem);
          }
          includeIndex = allIncludes.Count;

          if (stack.Count == 0) {
            break;
          }

          var include = stack.Pop();
          if (!includesFound.Add(include) || excludeFiles.Contains(include.CanonicalPath)) {
            continue;
          }

          DafnyFile file;
          try {
            file = new DafnyFile(include.IncludedFilename);
          } catch (IllegalDafnyFile) {
            return ($"Include of file \"{include.IncludedFilename}\" failed.");
          }

          string result = ParseFile(file, include, module, builtIns, errs, false, include.CompileIncludedCode);
          if (result != null) {
            return result;
          }
        }

        return null;
      }
    }

    private static string ParseFile(DafnyFile dafnyFile, Include include, ModuleDecl module, BuiltIns builtIns, Errors errs, bool verifyThisFile = true, bool compileThisFile = true) {
      var fn = DafnyOptions.O.UseBaseNameForFileName ? Path.GetFileName(dafnyFile.FilePath) : dafnyFile.FilePath;
      try {
        int errorCount = Dafny.Parser.Parse(dafnyFile.UseStdin, dafnyFile.SourceFileName, include, module, builtIns, errs, verifyThisFile, compileThisFile);
        if (errorCount != 0) {
          return $"{errorCount} parse errors detected in {fn}";
        }
      } catch (IOException e) {
        IToken tok = include == null ? Token.NoToken : include.tok;
        errs.SemErr(tok, "Unable to open included file");
        return $"Error opening file \"{fn}\": {e.Message}";
      }
      return null; // Success
    }

    public static async Task<(PipelineOutcome Outcome, PipelineStatistics Statistics)> BoogieOnce(
      TextWriter output,
      ExecutionEngine engine,
      string baseFile,
      string moduleName,
      Microsoft.Boogie.Program boogieProgram, string programId) {
      var moduleId = (programId ?? "main_program_id") + "_" + moduleName;
      var z3NotFoundMessage = @"
Z3 not found. Please either provide a path to the `z3` executable using
the `--solver-path <path>` option, manually place the `z3` directory
next to the `dafny` executable you are using (this directory should
contain `bin/z3` or `bin/z3.exe`), or set the PATH environment variable
to also include a directory containing the `z3` executable.
";

      var proverPath = DafnyOptions.O.ProverOptions.Find(o => o.StartsWith("PROVER_PATH="));
      if (proverPath is null && DafnyOptions.O.Verify) {
        Console.WriteLine(z3NotFoundMessage);
        return (PipelineOutcome.FatalError, new PipelineStatistics());
      }

      string bplFilename;
      if (DafnyOptions.O.PrintFile != null) {
        bplFilename = DafnyOptions.O.PrintFile;
      } else {
        string baseName = cce.NonNull(Path.GetFileName(baseFile));
        baseName = cce.NonNull(Path.ChangeExtension(baseName, "bpl"));
        bplFilename = Path.Combine(Path.GetTempPath(), baseName);
      }

      bplFilename = BoogieProgramSuffix(bplFilename, moduleName);
      var (outcome, stats) = await BoogiePipelineWithRerun(output, engine, boogieProgram, bplFilename,
        1 < DafnyOptions.O.VerifySnapshots ? moduleId : null);
      return (outcome, stats);
    }

    public static string BoogieProgramSuffix(string printFile, string suffix) {
      var baseName = Path.GetFileNameWithoutExtension(printFile);
      var dirName = Path.GetDirectoryName(printFile);

      return Path.Combine(dirName, baseName + "_" + suffix + Path.GetExtension(printFile));
    }

    public static bool IsBoogieVerified(PipelineOutcome outcome, PipelineStatistics statistics) {
      return (outcome == PipelineOutcome.Done || outcome == PipelineOutcome.VerificationCompleted)
         && statistics.ErrorCount == 0
         && statistics.InconclusiveCount == 0
         && statistics.TimeoutCount == 0
         && statistics.OutOfResourceCount == 0
         && statistics.OutOfMemoryCount == 0;
    }

    /// <summary>
    /// Resolve, type check, infer invariants for, and verify the given Boogie program.
    /// The intention is that this Boogie program has been produced by translation from something
    /// else.  Hence, any resolution errors and type checking errors are due to errors in
    /// the translation.
    /// The method prints errors for resolution and type checking errors, but still returns
    /// their error code.
    /// </summary>
    private static async Task<(PipelineOutcome Outcome, PipelineStatistics Statistics)> BoogiePipelineWithRerun(
      TextWriter output, ExecutionEngine engine, Microsoft.Boogie.Program/*!*/ program, string/*!*/ bplFileName,
        string programId) {
      Contract.Requires(program != null);
      Contract.Requires(bplFileName != null);

      var stats = new PipelineStatistics();
      var outcome = engine.ResolveAndTypecheck(program, bplFileName, out _);
      switch (outcome) {
        case PipelineOutcome.Done:
          return (outcome, stats);

        case PipelineOutcome.ResolutionError:
        case PipelineOutcome.TypeCheckingError:
          engine.PrintBplFile(bplFileName, program, false, false, DafnyOptions.O.PrettyPrint);
          Console.WriteLine();
          Console.WriteLine(
            "*** Encountered internal translation error - re-running Boogie to get better debug information");
          Console.WriteLine();

          var /*!*/ fileNames = new List<string /*!*/> { bplFileName };
          var reparsedProgram = engine.ParseBoogieProgram(fileNames, true);
          if (reparsedProgram != null) {
            engine.ResolveAndTypecheck(reparsedProgram, bplFileName, out _);
          }

          return (outcome, stats);

        case PipelineOutcome.ResolvedAndTypeChecked:
          engine.EliminateDeadVariables(program);
          engine.CollectModSets(program);
          engine.CoalesceBlocks(program);
          engine.Inline(program);
          var inferAndVerifyOutcome = await engine.InferAndVerify(output, program, stats, programId);
          return (inferAndVerifyOutcome, stats);

        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected outcome
      }
    }

  }
}