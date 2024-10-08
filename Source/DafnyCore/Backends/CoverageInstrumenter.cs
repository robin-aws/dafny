using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Bpl = Microsoft.Boogie;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.Compilers;

public class CoverageInstrumenter {
  private readonly SinglePassCodeGenerator codeGenerator;
  private List<(IToken, string)>/*?*/ legend;  // non-null implies options.CoverageLegendFile is non-null
  private string talliesFilePath;

  public CoverageInstrumenter(SinglePassCodeGenerator codeGenerator) {
    this.codeGenerator = codeGenerator;
    if (codeGenerator.Options?.CoverageLegendFile != null
        || codeGenerator.Options?.Get(CommonOptionBag.ExecutionCoverageReport) != null) {
      legend = new List<(IToken, string)>();
    }

    if (codeGenerator.Options?.Get(CommonOptionBag.ExecutionCoverageReport) != null) {
      talliesFilePath = Path.GetTempFileName();
    }
  }

  public bool IsRecording {
    get => legend != null;
  }

  public void Instrument(IToken tok, string description, ConcreteSyntaxTree wr) {
    Contract.Requires(tok != null);
    Contract.Requires(description != null);
    Contract.Requires(wr != null || !IsRecording);
    if (legend != null) {
      wr.Write("DafnyProfiling.CodeCoverage.Record({0})", legend.Count);
      codeGenerator.EndStmt(wr);
      legend.Add((tok, description));
    }
  }

  public void UnusedInstrumentationPoint(IToken tok, string description) {
    Contract.Requires(tok != null);
    Contract.Requires(description != null);
    if (legend != null) {
      legend.Add((tok, description));
    }
  }

  public void InstrumentExpr(IToken tok, string description, bool resultValue, ConcreteSyntaxTree wr) {
    Contract.Requires(tok != null);
    Contract.Requires(description != null);
    Contract.Requires(wr != null || !IsRecording);
    if (legend != null) {
      // The "Record" call always returns "true", so we negate it to get the value "false"
      wr.Write("{1}DafnyProfiling.CodeCoverage.Record({0})", legend.Count, resultValue ? "" : "!");
      legend.Add((tok, description));
    }
  }

  /// <summary>
  /// Should be called once "n" has reached its final value
  /// </summary>
  public void EmitSetup(ConcreteSyntaxTree wr) {
    Contract.Requires(wr != null);
    if (legend != null) {
      wr.Write("DafnyProfiling.CodeCoverage.Setup({0}", legend.Count);
      if (talliesFilePath != null) {
        wr.Write($", @\"{talliesFilePath}\"");
      }
      wr.Write(")");
      codeGenerator.EndStmt(wr);
    }
  }

  public void EmitTearDown(ConcreteSyntaxTree wr) {
    Contract.Requires(wr != null);
    if (legend != null) {
      wr.Write("DafnyProfiling.CodeCoverage.TearDown()");
      codeGenerator.EndStmt(wr);
    }
  }

  public void WriteLegendFile() {
    if (codeGenerator.Options?.CoverageLegendFile != null) {
      var filename = codeGenerator.Options.CoverageLegendFile;
      Contract.Assert(filename != null);
      TextWriter wr = filename == "-" ? codeGenerator.Options.OutputWriter : new StreamWriter(new FileStream(Path.GetFullPath(filename), FileMode.Create));
      {
        for (var i = 0; i < legend.Count; i++) {
          var e = legend[i];
          wr.WriteLine($"{i}: {e.Item1.TokenToString(codeGenerator.Options)}: {e.Item2}");
        }
      }
      legend = null;
    }
  }

  public async Task PopulateCoverageReport(CoverageReport coverageReport, Program program) {
    var coverageReportDir = codeGenerator.Options?.Get(CommonOptionBag.ExecutionCoverageReport);
    if (coverageReportDir != null) {
      // TODO: This is a expensive thing to do at this point.
      // Better to reuse the translation for earlier verification if it happened,
      // and probably do the translation earlier even with --no-verify
      var boogiePrograms = BoogieGenerator.Translate(program, program.Reporter).Select(p => p.Item2);
      var optionsWithoutVerify = new DafnyOptions(codeGenerator.Options);
      optionsWithoutVerify.Verify = false;
      using (var engine = Bpl.ExecutionEngine.CreateWithoutSharedCache(optionsWithoutVerify)) {
        foreach (var boogieProgram in boogiePrograms) {
          var (outcome, _) = await DafnyMain.BoogieOnce(new ErrorReporterSink(optionsWithoutVerify),
            optionsWithoutVerify, optionsWithoutVerify.OutputWriter, engine, "", "", boogieProgram, "programId");
        }
      }
      
      var tallies = File.ReadLines(talliesFilePath).Select(int.Parse).ToArray();
      foreach (var ((token, _), tally) in legend.Zip(tallies)) {
        var label = tally == 0 ? CoverageLabel.NotCovered : CoverageLabel.FullyCovered;
        var rangeTokenFromBlock = FindBasicBlockRange(boogiePrograms, token);
        var rangeToken = rangeTokenFromBlock ?? new RangeToken(new Token(token.line, 1), new Token(token.line + 1, 0));
        rangeToken.Uri = token.Uri;
        coverageReport.LabelCode(rangeToken, label);
      }
    }
  }

  private RangeToken FindBasicBlockRange(IEnumerable<Bpl.Program> boogiePrograms, IToken token) {
    foreach (var program in boogiePrograms) {
      foreach (var implementation in program.Implementations) {
        foreach (var block in implementation.Blocks) {
          RangeToken blockRange = RangeForBlock(block);
          if (blockRange != null && blockRange.Contains(token.pos)) {
            return blockRange;
          }
        }
      }
    }

    return null;
  }

  private RangeToken RangeForBlock(Bpl.Block block) {
    // TODO: Can a block be empty?
    Bpl.IToken bmin = block.cmds.MinBy(cmd => cmd.tok.line)?.tok;
    Bpl.IToken bmax = block.cmds.MaxBy(cmd => cmd.tok.line)?.tok;
    if (bmin == null || bmax == null) {
      return null;
    }
    IToken min = TokenForBoogieToken(bmin);
    IToken max = TokenForBoogieToken(bmax);
    return new RangeToken(min, max);
  }

  private IToken TokenForBoogieToken(Bpl.IToken token) {
    var result = new Token(token.line + 1, token.col + 1);
    result.pos = token.pos;
    return result;
  }

}
