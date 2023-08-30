//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class UnderspecificationDetector : ResolverPass {
    public UnderspecificationDetector(ModuleResolver resolver)
      : base(resolver) {
    }

    /// <summary>
    /// This method
    ///     * checks that type inference was able to determine all types
    ///         -- in calls to CheckPreTypeIsDetermined
    ///     * checks that shared destructors in datatypes are in agreement
    ///         -- in DatatypeDecl case of method Check
    ///     * checks that ORDINAL is used only where allowed
    ///         -- CheckContainsNoOrdinal, CheckTypeArgsContainNoOrdinal
    ///     * checks that bitvector literals are not too big for their type
    ///         -- in LiteralExpr case of VisitOneExpr
    ///     * fills in the .ResolvedOp field of binary expressions
    ///         -- in VisitOneExpr and BinaryExpr cases of VisitOneExpr
    /// </summary>
    public void Check(List<TopLevelDecl> declarations) {
      Contract.Requires(declarations != null);

      foreach (TopLevelDecl d in declarations) {
        var context = new UnderspecificationDetectorContext(d);
        CheckAttributes(d.Attributes, context);

        if (d is IteratorDecl) {
          var iter = (IteratorDecl)d;
          var prevErrCnt = ErrorCount;
          iter.Members.ForEach(CheckMember);
          if (prevErrCnt == ErrorCount) {
            iter.SubExpressions.ForEach(e => CheckExpression(e, context));
          }
          CheckParameterDefaultValues(iter.Ins, context);
          if (iter.Body != null) {
            CheckStatement(iter.Body, context);
            if (prevErrCnt == ErrorCount) {
              CheckStatement(iter.Body, context);
            }
          }

        } else if (d is SubsetTypeDecl) {
          var dd = (SubsetTypeDecl)d;
          CheckExpression(dd.Constraint, context);
          if (dd.Witness != null) {
            CheckExpression(dd.Witness, context);
          }

        } else if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          if (dd.Var != null) {
            if (!DetectUnderspecificationVisitor.IsDetermined(dd.BasePreType)) {
              ReportError(dd, "newtype's base type is not fully determined; add an explicit type for '{0}'", dd.Var.Name);
            }
            CheckExpression(dd.Constraint, context);
            if (dd.Witness != null) {
              CheckExpression(dd.Witness, context);
            }
          }
          CheckMembers(dd);

        } else if (d is DatatypeDecl) {
          var dd = (DatatypeDecl)d;
          foreach (var member in resolver.GetClassMembers(dd)!.Values) {
            if (member is DatatypeDestructor dtor) {
              var rolemodel = dtor.CorrespondingFormals[0];
              for (int i = 1; i < dtor.CorrespondingFormals.Count; i++) {
                var other = dtor.CorrespondingFormals[i];
                if (!Type.Equal_Improved(rolemodel.Type, other.Type)) {
                  ReportError(other.tok,
                    "shared destructors must have the same type, but '{0}' has type '{1}' in constructor '{2}' and type '{3}' in constructor '{4}'",
                    rolemodel.Name, rolemodel.Type, dtor.EnclosingCtors[0].Name, other.Type, dtor.EnclosingCtors[i].Name);
                } else if (rolemodel.IsGhost != other.IsGhost) {
                  ReportError(other.tok,
                    "shared destructors must agree on whether or not they are ghost, but '{0}' is {1} in constructor '{2}' and {3} in constructor '{4}'",
                    rolemodel.Name,
                    rolemodel.IsGhost ? "ghost" : "non-ghost", dtor.EnclosingCtors[0].Name,
                    other.IsGhost ? "ghost" : "non-ghost", dtor.EnclosingCtors[i].Name);
                }
              }
            }
          }
          foreach (var ctor in dd.Ctors) {
            CheckAttributes(ctor.Attributes, new UnderspecificationDetectorContext(ctor));
            CheckParameterDefaultValues(ctor.Formals, new UnderspecificationDetectorContext(ctor));
          }
          CheckMembers(dd);

        } else if (d is TopLevelDeclWithMembers md) {
          CheckMembers(md);
        }
      }
    }

    private void CheckMembers(TopLevelDeclWithMembers cl) {
      Contract.Requires(cl != null);
      foreach (var member in cl.Members) {
        CheckMember(member);
      }
    }

    /// <summary>
    /// Check that all pre-types of "member" have been filled in, and fill in all .ResolvedOp field.
    /// In addition, if "member" is an extreme predicate or extreme lemma, also do the checking for the corresponding
    /// prefix predicate or lemma. And, if "member" is a function by method, then also check the associated method.
    /// </summary>
    private void CheckMember(MemberDecl member) {
      var context = new UnderspecificationDetectorContext(member);
      CheckAttributes(member.Attributes, context);

      var errorCount = ErrorCount;
      if (member is ConstantField field) {
        if (field.Rhs != null) {
          CheckExpression(field.Rhs, context);
        }
        CheckPreType(field.PreType, context, field.tok, "const");

      } else if (member is Method method) {
        CheckParameterDefaultValues(method.Ins, context);
        method.Req.ForEach(mfe => CheckAttributedExpression(mfe, context));
        method.Reads.ForEach(mfe => CheckExpression(mfe.E, context));
        CheckSpecFrameExpression(method.Mod, context);
        method.Ens.ForEach(mfe => CheckAttributedExpression(mfe, context));
        CheckSpecExpression(method.Decreases, context);
        if (method.Body != null) {
          CheckStatement(method.Body, context);
        }
        if (errorCount == ErrorCount) {
          if (method is ExtremeLemma extremeLemma) {
            CheckMember(extremeLemma.PrefixLemma);
          }
        }

      } else if (member is Function function) {
        CheckParameterDefaultValues(function.Formals, context);
        function.Req.ForEach(e => CheckExpression(e.E, context));
        function.Ens.ForEach(e => CheckExpression(e.E, context));
        function.Reads.ForEach(fe => CheckExpression(fe.E, context));
        CheckSpecExpression(function.Decreases, context);
        if (function.Body != null) {
          CheckExpression(function.Body, context);
        }
        if (errorCount == ErrorCount) {
          if (function is ExtremePredicate extremePredicate) {
            CheckMember(extremePredicate.PrefixPredicate);
          } else if (function.ByMethodDecl != null) {
            CheckMember(function.ByMethodDecl);
          }
        }
      }
    }

    private void CheckPreType(PreType preType, UnderspecificationDetectorContext context, IToken tok, string whatIsBeingChecked) {
      var visitor = new DetectUnderspecificationVisitor(this, context);
      visitor.CheckPreTypeIsDetermined(tok, preType, whatIsBeingChecked);
    }

    private void CheckStatement(Statement stmt, UnderspecificationDetectorContext context) {
      Contract.Requires(stmt != null);
      var visitor = new DetectUnderspecificationVisitor(this, context);
      visitor.Visit(stmt);
    }

    private void CheckExpression(Expression expr, UnderspecificationDetectorContext context) {
      Contract.Requires(expr != null);
      var visitor = new DetectUnderspecificationVisitor(this, context);
      visitor.Visit(expr);
    }

    private void CheckSpecExpression(Specification<Expression> spec, UnderspecificationDetectorContext context) {
      CheckAttributes(spec.Attributes, context);
      spec.Expressions.ForEach(e => CheckExpression(e, context));
    }

    private void CheckSpecFrameExpression(Specification<FrameExpression> spec, UnderspecificationDetectorContext context) {
      CheckAttributes(spec.Attributes, context);
      spec.Expressions.ForEach(fe => CheckExpression(fe.E, context));
    }

    private void CheckAttributedExpression(AttributedExpression ae, UnderspecificationDetectorContext context) {
      CheckAttributes(ae.Attributes, context);
      CheckExpression(ae.E, context);
    }

    private void CheckAttributes(Attributes attributes, UnderspecificationDetectorContext context) {
      Attributes.SubExpressions(attributes).ForEach(e => CheckExpression(e, context));
    }

    private void CheckParameterDefaultValues(List<Formal> formals, UnderspecificationDetectorContext context) {
      foreach (var formal in formals) {
        if (formal.DefaultValue != null) {
          CheckExpression(formal.DefaultValue, context);
        }
      }
    }
  }

  public class UnderspecificationDetectorContext {
    private Declaration declaration;
    public bool IsExtremePredicate => declaration is ExtremePredicate;
    public bool IsExtremeLemma => declaration is ExtremeLemma;
    public UnderspecificationDetectorContext(Declaration declaration) {
      this.declaration = declaration;
    }
  }

  public class DetectUnderspecificationVisitor : BottomUpVisitor {
    private readonly UnderspecificationDetector cus;
    private readonly UnderspecificationDetectorContext context;

    public DetectUnderspecificationVisitor(UnderspecificationDetector cus, UnderspecificationDetectorContext context) {
      Contract.Requires(cus != null);
      Contract.Requires(context != null);
      this.cus = cus;
      this.context = context;
    }

    protected override void VisitOneStmt(Statement stmt) {
      if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        foreach (var local in s.Locals) {
          CheckPreTypeIsDetermined(local.Tok, local.PreType, "local variable");
          CheckTypeArgsContainNoOrdinal(local.Tok, local.PreType);
        }
      } else if (stmt is VarDeclPattern) {
        var s = (VarDeclPattern)stmt;
        s.LocalVars.ForEach(local => CheckPreTypeIsDetermined(local.Tok, local.PreType, "local variable"));
        s.LocalVars.ForEach(local => CheckTypeArgsContainNoOrdinal(local.Tok, local.PreType));

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        s.BoundVars.ForEach(bv => CheckPreTypeIsDetermined(bv.tok, bv.PreType, "bound variable"));
        s.BoundVars.ForEach(bv => CheckTypeArgsContainNoOrdinal(bv.tok, bv.PreType));

      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        if (s.AssumeToken == null) {
          var varLhss = new List<IVariable>();
          foreach (var lhs in s.Lhss) {
            var ide = (IdentifierExpr)lhs.Resolved;  // successful resolution implies all LHS's are IdentifierExpr's
            varLhss.Add(ide.Var);
          }
        }
        foreach (var lhs in s.Lhss) {
          CheckTypeArgsContainNoOrdinal(lhs.tok, lhs.PreType);
        }

      } else if (stmt is CalcStmt) {
        var s = (CalcStmt)stmt;
        // The resolution of the calc statement builds up .Steps and .Result, which are of the form E0 OP E1, where
        // E0 and E1 are expressions from .Lines.  These additional expressions still need to have their .ResolvedOp
        // fields filled in, so we visit them (but not their subexpressions) here.
        foreach (var e in s.Steps) {
          Visit(e);
        }
        Visit(s.Result);
      }
    }

    protected override void VisitOneExpr(Expression expr) {
      if (expr is DefaultValueExpression) {
        // skip this during underspecification detection, since it has yet to be filled in
        return;
      }

      var familyDeclName = PreTypeResolver.AncestorName(expr.PreType);

      if (expr is LiteralExpr) {
        var e = (LiteralExpr)expr;
        if (PreTypeResolver.IsBitvectorName(familyDeclName) || familyDeclName == "ORDINAL") {
          var n = (BigInteger)e.Value;
          var absN = n < 0 ? -n : n;
          // For bitvectors, check that the magnitude fits the width
          if (PreTypeResolver.IsBitvectorName(familyDeclName, out var width) && ModuleResolver.MaxBV(width) < absN) {
            cus.ReportError(e.tok, "literal ({0}) is too large for the bitvector type {1}", absN, e.PreType);
          }
          // For bitvectors and ORDINALs, check for a unary minus that, earlier, was mistaken for a negative literal
          // This can happen only in `match` patterns (see comment by LitPattern.OptimisticallyDesugaredLit).
          if (n < 0 || e.tok.val == "-0") {
            Contract.Assert(e.tok.val == "-0");  // this and the "if" above tests that "n < 0" happens only when the token is "-0"
            cus.ReportError(e.tok, "unary minus (-{0}, type {1}) not allowed in case pattern", absN, e.PreType);
          }
        }

        if (expr is StaticReceiverExpr stexpr) {
          CheckPreTypeIsDetermined(stexpr.tok, stexpr.PreType, "static receiver");
        }

      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        foreach (var bv in e.BoundVars) {
          CheckVariable(bv, "bound variable");
          if (context.IsExtremePredicate || context.IsExtremeLemma) {
            CheckContainsNoOrdinal(bv.tok, bv.PreType, $"type of bound variable '{bv.Name}' ('{bv.PreType}') is not allowed to use type ORDINAL");
          }
        }

      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        if (e.Member is Function || e.Member is Method) {
          var i = 0;
          foreach (var p in Util.Concat(e.PreTypeApplication_AtEnclosingClass, e.PreTypeApplication_JustMember)) {
            var tp =
              i < e.PreTypeApplication_AtEnclosingClass.Count
                ? e.Member.EnclosingClass.TypeArgs[i]
                : ((ICallable)e.Member).TypeArgs[i - e.PreTypeApplication_AtEnclosingClass.Count];
            if (!IsDetermined(p)) {
              cus.ReportError(e.tok, $"type parameter '{tp.Name}' (inferred to be '{p}') to the {e.Member.WhatKind} '{e.Member.Name}' could not be determined");
            } else {
              CheckContainsNoOrdinal(e.tok, p, $"type parameter '{tp.Name}' (passed in as '{p}') to the {e.Member.WhatKind} '{e.Member.Name}' is not allowed to use ORDINAL");
            }
            i++;
          }
        }

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        var i = 0;
        foreach (var p in Util.Concat(e.PreTypeApplication_AtEnclosingClass, e.PreTypeApplication_JustFunction)) {
          var tp =
            i < e.PreTypeApplication_AtEnclosingClass.Count
              ? e.Function.EnclosingClass.TypeArgs[i]
              : e.Function.TypeArgs[i - e.PreTypeApplication_AtEnclosingClass.Count];
          if (!IsDetermined(p)) {
            var hint = e.Name.StartsWith("reveal_") ? ". If you are making an opaque function, make sure that the function can be called." : "";
            cus.ReportError(e.tok, $"type parameter '{tp.Name}' (inferred to be '{p}') in the function call to '{e.Name}' could not be determined{hint}");
          } else {
            CheckContainsNoOrdinal(e.tok, p, $"type parameter '{tp.Name}' (passed in as '{p}') to function call '{e.Name}' is not allowed to use ORDINAL");
          }
          i++;
        }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        foreach (var lhsPattern in e.LHSs) {
          foreach (var bv in lhsPattern.Vars) {
            CheckVariable(bv, "bound variable");
            CheckTypeArgsContainNoOrdinal(bv.tok, bv.PreType);
          }
        }

      } else if (expr is IdentifierExpr) {
        // by specializing for IdentifierExpr, error messages will be clearer
        CheckPreTypeIsDetermined(expr.tok, expr.PreType, "variable");

      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        CheckPreTypeIsDetermined(e.tok, e.PreType, "cast target");

      } else if (expr is TypeTestExpr) {
        var e = (TypeTestExpr)expr;
        CheckPreTypeIsDetermined(e.tok, e.PreType, "type test target");

      } else if (CheckPreTypeIsDetermined(expr.tok, expr.PreType, "expression")) {
        if (expr is UnaryOpExpr uop) {
          var resolvedOp = (uop.Op, PreTypeResolver.AncestorName(uop.E.PreType)) switch {
            (UnaryOpExpr.Opcode.Not, "bool") => UnaryOpExpr.ResolvedOpcode.BoolNot,
            (UnaryOpExpr.Opcode.Cardinality, "set") => UnaryOpExpr.ResolvedOpcode.SetCard,
            (UnaryOpExpr.Opcode.Cardinality, "seq") => UnaryOpExpr.ResolvedOpcode.SeqLength,
            (UnaryOpExpr.Opcode.Cardinality, "multiset") => UnaryOpExpr.ResolvedOpcode.MultiSetCard,
            (UnaryOpExpr.Opcode.Cardinality, "map") => UnaryOpExpr.ResolvedOpcode.MapCard,
            (UnaryOpExpr.Opcode.Fresh, _) => UnaryOpExpr.ResolvedOpcode.Fresh,
            (UnaryOpExpr.Opcode.Allocated, _) => UnaryOpExpr.ResolvedOpcode.Allocated,
            (UnaryOpExpr.Opcode.Lit, _) => UnaryOpExpr.ResolvedOpcode.Lit,
            _ => UnaryOpExpr.ResolvedOpcode.YetUndetermined // Unreachable
          };
          if (uop.Op == UnaryOpExpr.Opcode.Not && PreTypeResolver.IsBitvectorName(familyDeclName)) {
            resolvedOp = UnaryOpExpr.ResolvedOpcode.BVNot;
          }
          uop.SetResolveOp(resolvedOp);

        } else if (expr is BinaryExpr) {
          var e = (BinaryExpr)expr;
          e.ResolvedOp = ResolveOp(e.Op, e.E0.PreType, e.E1.PreType);

        }
      }
    }

    /// Note: this method is allowed to be called even if "type" does not make sense for "op", as might be the case if
    /// resolution of the binary expression failed.  If so, an arbitrary resolved opcode is returned.
    /// Usually, the type of the right-hand operand is used to determine the resolved operator (hence, the shorter
    /// name "operandPreType" instead of, say, "rightOperandType").
    /// </summary>
    static BinaryExpr.ResolvedOpcode ResolveOp(BinaryExpr.Opcode op, PreType leftOperandPreType, PreType operandPreType) {
      Contract.Requires(leftOperandPreType != null);
      Contract.Requires(operandPreType != null);
      operandPreType = operandPreType.Normalize();
      var operandFamilyName = PreTypeResolver.AncestorName(operandPreType);
      switch (op) {
        case BinaryExpr.Opcode.Iff:
          return BinaryExpr.ResolvedOpcode.Iff;
        case BinaryExpr.Opcode.Imp:
          return BinaryExpr.ResolvedOpcode.Imp;
        case BinaryExpr.Opcode.Exp:
          return BinaryExpr.ResolvedOpcode.Imp;
        case BinaryExpr.Opcode.And:
          return BinaryExpr.ResolvedOpcode.And;
        case BinaryExpr.Opcode.Or:
          return BinaryExpr.ResolvedOpcode.Or;
        case BinaryExpr.Opcode.Eq:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.SetEq,
            "multiset" => BinaryExpr.ResolvedOpcode.MultiSetEq,
            "seq" => BinaryExpr.ResolvedOpcode.SeqEq,
            "map" or "imap" => BinaryExpr.ResolvedOpcode.MapEq,
            _ => BinaryExpr.ResolvedOpcode.EqCommon
          };
        case BinaryExpr.Opcode.Neq:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.SetNeq,
            "multiset" => BinaryExpr.ResolvedOpcode.MultiSetNeq,
            "seq" => BinaryExpr.ResolvedOpcode.SeqNeq,
            "map" or "imap" => BinaryExpr.ResolvedOpcode.MapNeq,
            _ => BinaryExpr.ResolvedOpcode.NeqCommon
          };
        case BinaryExpr.Opcode.Disjoint:
          return operandFamilyName == "multiset" ? BinaryExpr.ResolvedOpcode.MultiSetDisjoint : BinaryExpr.ResolvedOpcode.Disjoint;
        case BinaryExpr.Opcode.Lt: {
            if (operandPreType is DPreType dp && PreTypeResolver.AncestorDecl(dp.Decl) is IndDatatypeDecl) {
              return BinaryExpr.ResolvedOpcode.RankLt;
            }
            return operandFamilyName switch {
              "set" or "iset" => BinaryExpr.ResolvedOpcode.ProperSubset,
              "multiset" => BinaryExpr.ResolvedOpcode.ProperMultiSubset,
              "seq" => BinaryExpr.ResolvedOpcode.ProperPrefix,
              "char" => BinaryExpr.ResolvedOpcode.LtChar,
              _ => BinaryExpr.ResolvedOpcode.Lt
            };
          }
        case BinaryExpr.Opcode.Le:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.Subset,
            "multiset" => BinaryExpr.ResolvedOpcode.MultiSubset,
            "seq" => BinaryExpr.ResolvedOpcode.Prefix,
            "char" => BinaryExpr.ResolvedOpcode.LeChar,
            _ => BinaryExpr.ResolvedOpcode.Le
          };
        case BinaryExpr.Opcode.LeftShift:
          return BinaryExpr.ResolvedOpcode.LeftShift;
        case BinaryExpr.Opcode.RightShift:
          return BinaryExpr.ResolvedOpcode.RightShift;
        case BinaryExpr.Opcode.Add:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.Union,
            "multiset" => BinaryExpr.ResolvedOpcode.MultiSetUnion,
            "seq" => BinaryExpr.ResolvedOpcode.Concat,
            "map" or "imap" => BinaryExpr.ResolvedOpcode.MapMerge,
            _ => BinaryExpr.ResolvedOpcode.Add
          };
        case BinaryExpr.Opcode.Sub: {
            var leftFamilyName = PreTypeResolver.AncestorName(leftOperandPreType);
            if (leftFamilyName == "map" || leftFamilyName == "imap") {
              return BinaryExpr.ResolvedOpcode.MapSubtraction;
            }
            return operandFamilyName switch {
              "set" or "iset" => BinaryExpr.ResolvedOpcode.SetDifference,
              "multiset" => BinaryExpr.ResolvedOpcode.MultiSetDifference,
              _ => BinaryExpr.ResolvedOpcode.Sub
            };
          }
        case BinaryExpr.Opcode.Mul:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.Intersection,
            "multiset" => BinaryExpr.ResolvedOpcode.MultiSetIntersection,
            _ => BinaryExpr.ResolvedOpcode.Mul
          };
        case BinaryExpr.Opcode.Gt: {
            if (operandPreType is DPreType dp && PreTypeResolver.AncestorDecl(dp.Decl) is IndDatatypeDecl) {
              return BinaryExpr.ResolvedOpcode.RankGt;
            }
            return operandFamilyName switch {
              "set" or "iset" => BinaryExpr.ResolvedOpcode.ProperSuperset,
              "multiset" => BinaryExpr.ResolvedOpcode.ProperMultiSuperset,
              "char" => BinaryExpr.ResolvedOpcode.GtChar,
              _ => BinaryExpr.ResolvedOpcode.Gt
            };
          }
        case BinaryExpr.Opcode.Ge:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.Superset,
            "multiset" => BinaryExpr.ResolvedOpcode.MultiSuperset,
            "char" => BinaryExpr.ResolvedOpcode.GeChar,
            _ => BinaryExpr.ResolvedOpcode.Ge
          };
        case BinaryExpr.Opcode.In:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.InSet,
            "multiset" => BinaryExpr.ResolvedOpcode.InMultiSet,
            "map" or "imap" => BinaryExpr.ResolvedOpcode.InMap,
            _ => BinaryExpr.ResolvedOpcode.InSeq
          };
        case BinaryExpr.Opcode.NotIn:
          return operandFamilyName switch {
            "set" or "iset" => BinaryExpr.ResolvedOpcode.NotInSet,
            "multiset" => BinaryExpr.ResolvedOpcode.NotInMultiSet,
            "map" or "imap" => BinaryExpr.ResolvedOpcode.NotInMap,
            _ => BinaryExpr.ResolvedOpcode.NotInSeq
          };
        case BinaryExpr.Opcode.Div:
          return BinaryExpr.ResolvedOpcode.Div;
        case BinaryExpr.Opcode.Mod:
          return BinaryExpr.ResolvedOpcode.Mod;
        case BinaryExpr.Opcode.BitwiseAnd:
          return BinaryExpr.ResolvedOpcode.BitwiseAnd;
        case BinaryExpr.Opcode.BitwiseOr:
          return BinaryExpr.ResolvedOpcode.BitwiseOr;
        case BinaryExpr.Opcode.BitwiseXor:
          return BinaryExpr.ResolvedOpcode.BitwiseXor;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();  // unexpected operator
      }
    }

    void CheckVariable(IVariable v, string whatIsBeingChecked) {
      if (!IsDetermined(v.PreType)) {
        cus.ReportError(v.Tok, $"type of {whatIsBeingChecked} '{v.Name}' could not be determined{UndeterminedPreTypeToString(v.PreType)}; please specify the type explicitly");
      }
    }

    private string UndeterminedPreTypeToString(PreType preType) {
      if (preType.Normalize() is PreTypeProxy) {
        return "";
      } else {
        return $" ('{preType}')";
      }
    }

    public static bool IsDetermined(PreType pt) {
      Contract.Requires(pt != null);
      if (pt.Normalize() is DPreType dp) {
        if (dp.PrintablePreType != null) {
          // If the type is a synonym, focus on it, which will check that all its type arguments have been filled in
          dp = dp.PrintablePreType;
        }
        Contract.Assert(dp.Decl != null); // every DPreType has a non-null .Decl
        return dp.Arguments.TrueForAll(IsDetermined);
      }
      return false;
    }

    private readonly ISet<PreTypeProxy> underspecifiedTypeProxies = new HashSet<PreTypeProxy>();

    /// <summary>
    /// Check if "pt" is fully determined. If it is, return "true". If it is not, then
    /// report an error and return "false".
    /// </summary>
    public bool CheckPreTypeIsDetermined(IToken tok, PreType pt, string whatIsBeingChecked, PreType origPreType = null) {
      Contract.Requires(tok != null);
      Contract.Requires(pt != null);
      Contract.Requires(whatIsBeingChecked != null);
      origPreType ??= pt;
      pt = pt.Normalize();

      if (pt is PreTypeProxy proxy) {
        if (!underspecifiedTypeProxies.Contains(proxy)) {
          // report an error for this TypeProxy only once
          cus.ReportError(tok, $"the type{UndeterminedPreTypeToString(origPreType)} of this {whatIsBeingChecked} is underspecified");
          underspecifiedTypeProxies.Add(proxy);
        }
        return false;
      }
      var dp = (DPreType)pt;
      if (dp.PrintablePreType != null) {
        // If the type is a synonym, focus on it, which will check that all its type arguments have been filled in
        dp = dp.PrintablePreType;
      }
      // Recurse on type arguments:
      return dp.Arguments.TrueForAll(tt => CheckPreTypeIsDetermined(tok, tt, whatIsBeingChecked, origPreType));
    }

    public void CheckTypeArgsContainNoOrdinal(IToken tok, PreType preType) {
      Contract.Requires(tok != null);
      Contract.Requires(preType != null);
      if (preType.Normalize() is DPreType dp) {
        dp.Arguments.ForEach(tt => CheckContainsNoOrdinal(tok, tt, "an ORDINAL type is not allowed to be used as a type argument"));
      }
    }

    public void CheckContainsNoOrdinal(IToken tok, PreType preType, string errMsg) {
      Contract.Requires(tok != null);
      Contract.Requires(preType != null);
      Contract.Requires(errMsg != null);
      if (preType.Normalize() is DPreType dp) {
        if (PreTypeResolver.AncestorName(dp) == "ORDINAL") {
          cus.ReportError(tok, errMsg);
        }
        dp.Arguments.ForEach(tt => CheckContainsNoOrdinal(tok, tt, errMsg));
      }
    }
  }
}
