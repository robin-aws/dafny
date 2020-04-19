include "./List.dfy"

module ExternalCollections {

  import opened Collections

  trait {:extern} ExternalList {

    // TODO-RS: It may be possible to avoid the duplicate definitions of
    // Valid() and Repr if this trait could extend ExternallyValid itself
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
    ghost var Repr: set<object>

    // TODO-RS: figure out how to enforce that this acts like a function
    function method Length(): int 
      requires Valid()
      reads Repr
    
    method Get(i: int) returns (res: int)
      modifies Repr
    
    method Set(i: int, element: int)
      modifies Repr
    
    method Add(element: int)
      modifies Repr
  }

  /*
   * Adapts a Dafny-internal List as an ExternalList
   */
  class AsExternalList extends ExternalList {

    var wrapped: List

    constructor(wrapped: List) 
      requires wrapped.Valid()
      ensures Valid()
    {
      this.wrapped := wrapped;
      this.Repr := {this} + wrapped.Repr;
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
    {
      && wrapped in Repr
      && Repr == {this} + wrapped.Repr
      && wrapped.Valid()
    }

    function method Length(): int
      requires Valid()
      reads Repr
    {
      wrapped.Length()
    }
    
    method Get(i: int) returns (res: int)
    {
      expect 0 <= i < wrapped.Length();
      res := wrapped.Get(i);
    }
    
    method Set(i: int, element: int)
    {
      expect 0 <= i < wrapped.Length();
      expect 0 <= element;
      wrapped.Set(i, element);
    }
    
    method Add(element: int)
      modifies Repr
      ensures fresh(Repr - old(Repr))
    {
      expect 0 <= element;
      wrapped.Add(element);
    }
  }

  /*
   * Adapts an ExternalList as a Dafny-internal List
   */
  class AsList extends List {

    var wrapped: ExternalList

    constructor(wrapped: ExternalList) 
      requires wrapped.Valid()
      ensures Valid()
    {
      this.wrapped := wrapped;
      this.Repr := {this} + wrapped.Repr;
    }

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr 
    {
      && wrapped in Repr
      && Repr == {this} + wrapped.Repr
      && wrapped.Valid()
    }

    function method Length(): nat
      requires Valid()
      reads this, Repr
      ensures Length() == |values|
    {
      var result := wrapped.Length();
      // TODO-RS: Ideally we would include `expect result >= 0;`, but
      // we can't currently do that in a function, even though we really want that in
      // the compiled version.
      Axiom(result == |values|);
      result
    }
    
    method Get(i: int) returns (res: nat)
      requires Valid()
      requires 0 <= i < Length()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Length() == old(Length())
      ensures res == values[i]
    {
      var result := wrapped.Get(i);
      expect 0 <= result;
      res := result;
      
      Axiom(Length() == old(Length()));
      Axiom(res == values[i]);
    }
    
    method Set(i: int, element: nat)
      requires Valid()
      requires 0 <= i < Length()
      decreases Repr
      modifies Repr
      ensures Valid()
      ensures values == old(values[..i]) + [element] + old(values[i + 1..])
      ensures fresh(Repr - old(Repr))
    {
      wrapped.Set(i, element);

      // Presumably cheap sanity check. This will be a tradeoff on a per-operation basis.
      var elementAfter := wrapped.Get(i);
      expect elementAfter == element;

      values := values[..i] + [element] + values[i + 1..];
    }

    method Add(element: nat)
      requires Valid()
      decreases Repr
      modifies Repr
      ensures Valid()
      ensures values == old(values) + [element]
      ensures fresh(Repr - old(Repr))
    {
      var lengthBefore := Length();

      wrapped.Add(element);

      values := values + [element];

      expect Length() == lengthBefore + 1;
    }
  }

  // TODO-RS: Replace with `expect {:axiom} ...` when supported.
  lemma {:axiom} Axiom(p: bool) ensures p
}