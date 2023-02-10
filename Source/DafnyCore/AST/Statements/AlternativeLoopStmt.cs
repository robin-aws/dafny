using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class AlternativeLoopStmt : LoopStmt, ICloneable<AlternativeLoopStmt>, ICanFormat {
  public readonly bool UsesOptionalBraces;
  public readonly List<GuardedAlternative> Alternatives;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(Alternatives != null);
  }

  public AlternativeLoopStmt Clone(Cloner cloner) {
    return new AlternativeLoopStmt(cloner, this);
  }

  public AlternativeLoopStmt(Cloner cloner, AlternativeLoopStmt original) : base(cloner, original) {
    Alternatives = original.Alternatives.ConvertAll(cloner.CloneGuardedAlternative);
    UsesOptionalBraces = original.UsesOptionalBraces;
  }

  public AlternativeLoopStmt(RangeToken rangeToken,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    List<GuardedAlternative> alternatives, bool usesOptionalBraces)
    : base(rangeToken, invariants, decreases, mod) {
    Contract.Requires(alternatives != null);
    this.Alternatives = alternatives;
    this.UsesOptionalBraces = usesOptionalBraces;
  }
  public AlternativeLoopStmt(RangeToken rangeToken,
    List<AttributedExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
    List<GuardedAlternative> alternatives, bool usesOptionalBraces, Attributes attrs)
    : base(rangeToken, invariants, decreases, mod, attrs) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(alternatives != null);
    this.Alternatives = alternatives;
    this.UsesOptionalBraces = usesOptionalBraces;
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      foreach (var alt in Alternatives) {
        foreach (var s in alt.Body) {
          yield return s;
        }
      }
    }
  }

  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      foreach (var alt in Alternatives) {
        foreach (var e in Attributes.SubExpressions(alt.Attributes)) {
          yield return e;
        }
      }
    }
  }

  public override IEnumerable<Expression> NonSpecificationSubExpressions {
    get {
      foreach (var e in base.NonSpecificationSubExpressions) { yield return e; }
      foreach (var alt in Alternatives) {
        yield return alt.Guard;
      }
    }
  }

  public override IEnumerable<Node> Children => SpecificationSubExpressions.Concat<Node>(Alternatives);
  public bool SetIndent(int indentBefore, TokenNewIndentCollector formatter) {
    return formatter.SetIndentCases(indentBefore, OwnedTokens.Concat(Alternatives.SelectMany(alternative => alternative.OwnedTokens)), () => {
      foreach (var ens in Invariants) {
        formatter.SetAttributedExpressionIndentation(ens, indentBefore + formatter.SpaceTab);
      }

      foreach (var dec in Decreases.Expressions) {
        formatter.SetDecreasesExpressionIndentation(dec, indentBefore + formatter.SpaceTab);
      }

      formatter.VisitAlternatives(Alternatives, indentBefore);
      if (EndToken.val == "}") {
        formatter.SetClosingIndentedRegion(EndToken, indentBefore);
      }
    });
  }
}