include "./List.dfy"

module ExternalCollections {

  import opened Collections

  trait {:extern} ExternalList {

    // TODO-RS: apply my "external invariant" strategy for ensuring externally-visible
    // object are always Valid()

    // TODO-RS: Can we make this "true" by default, so external implementations are 
    // assumed to be always valid through things like access control and critical sections?
    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr

    // TODO-RS: Similarly, can we assign this to {} or {this} by default somehow?
    ghost var Repr: set<object>

    // TODO-RS: figure out how to enforce that this acts like a function
    function method Length(): int
      requires Valid()
      reads Repr
      ensures Valid()
    
    method Get(i: int) returns (res: int)
      requires Valid()
      decreases Repr
    
    method Set(i: int, element: int)
      requires Valid()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    
    method Add(element: int)
      requires Valid()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
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
      && wrapped in wrapped.Repr
      && this !in wrapped.Repr
      && wrapped.Repr <= Repr
      && wrapped.Valid()
    }

    function method Length(): int
      requires Valid()
      reads Repr
    {
      wrapped.Length()
    }
    
    method Get(i: int) returns (res: int)
      requires Valid()
      decreases Repr
    {
      expect 0 <= i < wrapped.Length();
      res := wrapped.Get(i);
    }
    
    method Set(i: int, element: int)
      requires Valid()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    {
      expect 0 <= i < wrapped.Length();
      expect 0 <= element;
      wrapped.Set(i, element);
      Repr := {this} + wrapped.Repr;
    }
    
    method Add(element: int)
      requires Valid()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    {
      expect 0 <= element;
      wrapped.Add(element);
      Repr := {this} + wrapped.Repr;
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
      && wrapped in wrapped.Repr
      && this !in wrapped.Repr
      && wrapped.Repr <= Repr
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
      // TODO-RS: Replace with `expect {:axiom} ...` when supported.
      assume result == |values|;
      result
    }
    
    method Get(i: int) returns (res: nat)
      requires Valid()
      requires 0 <= i < Length()
      decreases Repr
      ensures res == values[i]
    {
      var result := wrapped.Get(i);
      expect 0 <= result;
      res := result;
      
      // TODO-RS: Replace with `expect {:axiom} ...` when supported.
      assume res == values[i];
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

      // Presumably cheap sanity check
      var elementAfter := wrapped.Get(i);
      expect elementAfter == element;

      values := values[..i] + [element] + values[i + 1..];
      Repr := {this} + wrapped.Repr;
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
      Repr := {this} + wrapped.Repr;

      expect Length() == lengthBefore + 1;
    }
  }
}