using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// Class "BreakStmt" represents both "break" and "continue" statements.
/// </summary>
public class BreakStmt : Statement, IHasReferences, ICloneable<BreakStmt> {
  public readonly IToken TargetLabel;
  public readonly bool IsContinue;
  public string Kind => IsContinue ? "continue" : "break";
  public readonly int BreakAndContinueCount;
  [FilledInDuringResolution] public Statement TargetStmt;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(TargetLabel != null || 1 <= BreakAndContinueCount);
  }

  public BreakStmt Clone(Cloner cloner) {
    return new BreakStmt(cloner, this);
  }

  public BreakStmt(Cloner cloner, BreakStmt original) : base(cloner, original) {
    TargetLabel = original.TargetLabel;
    IsContinue = original.IsContinue;
    BreakAndContinueCount = original.BreakAndContinueCount;
    if (cloner.CloneResolvedFields) {
      TargetStmt = cloner.CloneStmt(original.TargetStmt, true);
    }
  }

  public BreakStmt(RangeToken rangeToken, IToken targetLabel, bool isContinue, Attributes attributes = null)
    : base(rangeToken, attributes) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(targetLabel != null);
    this.TargetLabel = targetLabel;
    this.IsContinue = isContinue;
  }

  /// <summary>
  /// For "isContinue == false", represents the statement "break ^breakAndContinueCount ;".
  /// For "isContinue == true", represents the statement "break ^(breakAndContinueCount - 1) continue;".
  /// </summary>
  public BreakStmt(RangeToken rangeToken, int breakAndContinueCount, bool isContinue, Attributes attributes = null)
    : base(rangeToken, attributes) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(1 <= breakAndContinueCount);
    this.BreakAndContinueCount = breakAndContinueCount;
    this.IsContinue = isContinue;
  }

  public IEnumerable<IHasNavigationToken> GetReferences() {
    return new[] { TargetStmt }.OfType<IHasNavigationToken>();
  }

  public IToken NavigationToken => Tok;
}