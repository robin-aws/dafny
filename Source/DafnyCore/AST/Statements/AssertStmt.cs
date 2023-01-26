using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class AssertStmt : PredicateStmt, ICloneable<AssertStmt> {
  public readonly BlockStmt Proof;
  public readonly AssertLabel Label;

  public AssertStmt Clone(Cloner cloner) {
    return new AssertStmt(cloner, this);
  }

  public AssertStmt(Cloner cloner, AssertStmt original) : base(cloner, original) {
    Proof = cloner.CloneBlockStmt(original.Proof);
    Label = original.Label == null ? null : new AssertLabel(cloner.Tok(original.Label.Tok), original.Label.Name);
  }

  public AssertStmt(RangeToken rangeToken, Expression expr, BlockStmt/*?*/ proof, AssertLabel/*?*/ label, Attributes attrs)
    : base(rangeToken, expr, attrs) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(expr != null);
    Proof = proof;
    Label = label;
  }
  public override IEnumerable<Statement> SubStatements {
    get {
      if (Proof != null) {
        yield return Proof;
      }
    }
  }
  public void AddCustomizedErrorMessage(IToken tok, string s) {
    var args = new List<Expression>() { new StringLiteralExpr(tok, s, true) };
    IToken openBrace = tok;
    IToken closeBrace = new Token(tok.line, tok.col + 7 + s.Length + 1); // where 7 = length(":error ")
    this.Attributes = new UserSuppliedAttributes(tok, openBrace, closeBrace, args, this.Attributes);
  }

  public override IEnumerable<Expression> SpecificationSubExpressions {
    get {
      foreach (var e in base.SpecificationSubExpressions) { yield return e; }
      yield return Expr;
    }
  }
}