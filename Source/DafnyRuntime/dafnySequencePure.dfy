
include "../../Test/libraries/src/JSON/Stacks.dfy"

module {:options "/functionSyntax:4"} MetaSeq {

  import opened Stacks

  datatype SeqExpr<T> = Empty | Direct(a: seq<T>) | Concat(left: SeqExpr<T>, right: SeqExpr<T>, length: nat) {

    predicate Valid() {
      match this
      case Concat(left, right, length) => 
        && left.Valid()
        && right.Valid()
        && left.Length() + right.Length() == length
      case _ => true
    }

    function Length(): nat {
      match this
      case Empty => 0
      case Direct(a) => |a|
      case Concat(_, _, length) => length
    }

    function At(i: nat): T 
      requires Valid()
      requires i < Length()
    {
      Force()[i]
    }

    function Concatenate(s: SeqExpr<T>): SeqExpr<T> {
      Concat(this, s, Length() + s.Length())
    }

    method Slice(start: nat, end: nat) returns (s: SeqExpr<T>)
      requires start <= end <= Length()

    function Value(): seq<T> 
      requires Valid()
      ensures |Value()| == Length()
    {
      match this
      case Empty => []
      case Direct(a) => a
      case Concat(left, right, _) => left.Value() + right.Value()
    }

    // TODO: {:memoize} should result in thread-safe lazy evaluation in each runtime
    function {:memoize} Force(): seq<T> 
      requires Valid()
    {
      Value()
    } by method {
      match this
      case Concat(left, right, length) => return CalcConcat(left, right, length);
      case _ => return Value();
    }
  }

  function CalcConcat<T>(left: SeqExpr<T>, right: SeqExpr<T>, length: nat): seq<T> {
    left.Value() + right.Value()
  } by method {
    var builder: SeqBuilder<T> := new SeqBuilder(length);
    var toVisit := new Stack<SeqExpr<T>>(Empty);
    :- expect toVisit.Push(right);
    :- expect toVisit.Push(left);

    while (0 < toVisit.size) 
      invariant toVisit.Valid?()
      invariant fresh(toVisit)
      invariant fresh(toVisit.data)
    {
      // TODO: Have to add Pop() to Stacks.dfy
      var next := toVisit.Pop();

      match next
      case Concat(nextLeft, nextRight, _) => {
        // No way to grab the result of Force() here if present, but that's okay
        :- expect toVisit.Push(nextRight);
        :- expect toVisit.Push(nextLeft);
      }
      case _ => {
        builder.Append(next.Value());
      }
    }
    
    return builder.Value();
  }

  // TODO: Make this an extern. How to monomorphize?
  class SeqBuilder<T> {
    var s: seq<T>

    constructor(length: nat) 
      ensures Value() == []
    {
      s := [];
    }

    method Append(t: seq<T>) 
      modifies this
      ensures Value() == old(Value()) + t
    {
      s := s + t;
    }

    function Value(): seq<T> reads this {
      s
    }
  }
}