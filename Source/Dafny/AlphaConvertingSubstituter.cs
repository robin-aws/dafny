using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  /// <summary>
  /// This substituter performs substitutions in such a way that it's okay to print the resulting expression without a human getting confused.
  /// More precisely, bound variables first gets alpha-renamed.  Also, "this" is never left implicit, including in the
  /// case where "receiverReplacement" is given as ImplicitThisExpr (but no attempt is made to substitute for all ImplicitThisExpr's in
  /// "receiverReplacement" and the range of "substMap").
  /// </summary>
  public class AlphaConvertingSubstituter : Substituter {
    public AlphaConvertingSubstituter(Expression receiverReplacement, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap)
      : base(receiverReplacement is ImplicitThisExpr ? new ThisExpr(receiverReplacement.tok) { Type = receiverReplacement.Type } : receiverReplacement, substMap, typeMap) {
      Contract.Requires(substMap != null);
      Contract.Requires(typeMap != null);
    }
    protected override List<BoundVar> CreateBoundVarSubstitutions(List<BoundVar> vars, bool forceSubstitutionOfBoundVars) {
      var newBoundVars = vars.Count == 0 ? vars : new List<BoundVar>();
      foreach (var bv in vars) {
        var tt = Resolver.SubstType(bv.Type, typeMap);
        var newName = "_'" + bv.Name;
        
        var newDomain = bv.Domain == null ? null : Substitute(bv.Domain);

        // update substMap to reflect the new BoundVar substitutions
        var ie = new IdentifierExpr(bv.tok, newName);
        substMap.Add(bv, ie);
        
        var newRange = bv.Range == null ? null : Substitute(bv.Range);
        
        var newBv = new BoundVar(bv.tok, newName, tt, newDomain, newRange);
        newBoundVars.Add(newBv);
        
        ie.Var = newBv;  // resolve here
        ie.Type = newBv.Type;  // resolve here
      }
      return newBoundVars;
    }
  }
}