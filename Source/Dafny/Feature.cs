using System;
using Microsoft.Boogie;

namespace Microsoft.Dafny.Feature {

  public interface Feature {

    public string DisplayName { get; }
    
    public string DocumentationURL { get; }
    
    public bool FindUse(Program program);
  }
  
  public class IntegersFeature : Feature {
    public string DisplayName => "Integers";
    public string DocumentationURL => "https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#sec-numeric-types";
    public bool FindUse(Program program) {
      var finder = new IntegerFinder();
      bool dummy = false;
      // finder.Visit(program, ref dummy);
      return false;
    }
  }

  public class IntegerFinder : TopDownVisitor<bool> {
    protected virtual bool VisitOneExpr(Expression expr, ref bool dummy) {
      if (expr.Type is IntType) {
        return false;
      }

      return true;
    }
  }
}