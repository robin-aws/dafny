include "./List.dfy"
include "./ExternalInvariants.dfy"

module ExternalCollections {

  import opened Collections
  import opened ExternalInvariants

  class ValidatableList extends ExternallyValid {
    
    const list: List
    
    constructor(list: List) 
      requires list.Valid()
      ensures Valid()
    {
      this.list := list;
      this.Repr := {this, list} + list.Repr;
      this.ValidatableRepr := {this};
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      ensures Valid() ==> forall v :: v in ValidatableRepr ==> v.Repr <= Repr
      ensures Valid() ==> forall v :: v in ValidatableRepr && v != this ==> this !in v.Repr 
    {
      && list in Repr
      && Repr == {this, list} + list.Repr
      && ValidatableRepr == {this}
      && list.Repr <= Repr
      && list.Valid()
    }

    twostate lemma IndependentValidity()
      requires old(Valid())
      requires unchanged(this, Repr - ValidatableRepr)
      requires forall v :: v in ValidatableRepr && v != this ==> v.Valid()
      ensures Valid()
    {
    }
  }

  trait {:extern} ExternalList {

    // TODO-RS: It may be possible to avoid the duplicate definitions of
    // Valid() and Repr if this trait could extend ExternallyValid itself
    predicate ExtValid() 
      reads this, ExtRepr 
      ensures ExtValid() ==> this in ExtRepr
    ghost var ExtRepr: set<object>

    // TODO-RS: figure out how to enforce that this acts like a function
    function method Length(): int
    
    method Get(i: int) returns (res: int)
      requires AllValid(set v: ExternallyValid | allocated(v) && v.P())
      modifies ExtRepr
      ensures AllValid(set v: ExternallyValid | allocated(v) && v.P())
    
    method Set(i: int, element: int)
      requires AllValid(set v: ExternallyValid | allocated(v) && v.P())
      modifies ExtRepr
      ensures AllValid(set v: ExternallyValid | allocated(v) && v.P())
    
    method Add(element: int)
      requires AllValid(set v: ExternallyValid | allocated(v) && v.P())
      modifies ExtRepr
      ensures AllValid(set v: ExternallyValid | allocated(v) && v.P())
  }

  /*
   * Adapts a Dafny-internal List as an ExternalList
   */
  class AsExternalList extends ExternalList, ExternallyValid {

    var wrapped: ValidatableList

    constructor(wrapped: List) 
      requires wrapped.Valid()
      ensures Valid()
    {
      this.wrapped := new ValidatableList(wrapped);
      this.Repr := {this} + wrapped.Repr;
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      ensures Valid() ==> forall v :: v in ValidatableRepr ==> v.Repr <= Repr
      ensures Valid() ==> forall v :: v in ValidatableRepr && v != this ==> this !in v.Repr
      ensures Valid() ==> ExtValid()
    {
      && wrapped in Repr
      && Repr == {this} + wrapped.Repr
      && wrapped.Valid()
      && ExtRepr == Repr
      && ExtValid()
    }

    predicate ExtValid() 
      reads this, ExtRepr 
      ensures ExtValid() ==> this in ExtRepr
    {
      && wrapped in ExtRepr
      && ExtRepr == {this} + wrapped.Repr
      && wrapped.Valid()
      && ExtRepr == Repr
    }

    twostate lemma IndependentValidity()
      requires old(Valid())
      requires unchanged(this)
      requires forall v :: v in ValidatableRepr && v != this ==> v.Valid()
      ensures Valid() {

      }

    function method Length(): int
      reads Repr
    {
      wrapped.list.Length()
    }
    
    method Get(i: int) returns (res: int)
      requires AllValid(set v: ExternallyValid | allocated(v) && v.P())
      ensures AllValid(set v: ExternallyValid | allocated(v) && v.P())
    {
      AllValidMakesMeValid();
      expect 0 <= i < wrapped.list.Length();
      res := wrapped.list.Get(i);
    }
    
    method Set(i: int, element: int)
      requires Valid()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
    {
      expect 0 <= i < wrapped.list.Length();
      expect 0 <= element;
      wrapped.list.Set(i, element);
    }
    
    method Add(element: int)
      requires AllValid(set v: ExternallyValid | allocated(v) && v.P())
      modifies ExtRepr
      ensures AllValid(set v: ExternallyValid | allocated(v) && v.P())
      ensures fresh(Repr - old(Repr))
    {
      AllValidMakesMeValid();
      expect 0 <= element;
      wrapped.list.Add(element);
    }
  }

  /*
   * Adapts an ExternalList as a Dafny-internal List
   */
  class AsList extends List {

    var wrapped: ExternalList

    constructor(wrapped: ExternalList) 
      ensures Valid()
    {
      this.wrapped := wrapped;
      this.Repr := {this};
    }

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr 
    {
      && Repr == {this}
      && wrapped.ExtValid()
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
      decreases Repr
      ensures res == values[i]
    {
      var result := wrapped.Get(i);
      expect 0 <= result;
      res := result;
      
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