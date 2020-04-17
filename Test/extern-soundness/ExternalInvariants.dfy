
module ExternalInvariants {

  trait {:termination false} ExternallyValid {
    ghost const Repr: set<object>
    ghost const ValidatableRepr: set<ExternallyValid>
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> 
        && this in Repr
        && ValidatableRepr <= Repr
        && (forall v :: v in ValidatableRepr ==> v.Repr <= Repr)
        && (forall v :: v in ValidatableRepr && v != this ==> this !in v.Repr)
    
    // Dummy predicate to avoid "/!\ No terms found to trigger on." warning
    predicate P() {
      true
    }

    // Lemma for re-establishing the external invariant after one object
    // has changed from valid state to another valid state. Asserts that
    // all OTHER previously valid objects are still valid based on their
    // IndependentValidity() lemma.
    twostate lemma AllStillValid() 
      requires old(AllValid(set v: ExternallyValid | allocated(v) && v.P()))
      requires Valid()
      requires forall o :: o !in ValidatableRepr ==> unchanged(o)
      requires forall o :: o in ValidatableRepr ==> o.Valid()
      ensures AllValid(set v: ExternallyValid | allocated(v) && v.P())
    {
      forall v: ExternallyValid | old(allocated(v)) && v.P() ensures v.Valid() {
        IndependentValidityInductive(v, ValidatableRepr);
      }
    }

    // Lemma that must be proved for each implementing class. Usually
    // proves itself with an empty body, provided Valid() is defined
    // in a compatible way.
    twostate lemma IndependentValidity()
      requires old(Valid())
      requires unchanged(this, Repr - ValidatableRepr)
      requires forall v :: v in ValidatableRepr && v != this ==> v.Valid()
      ensures Valid()

    // Slightly silly lemma that might go away if we tweak Dafny's heuristics a bit
    lemma AllValidMakesMeValid() 
      requires AllValid(set v: ExternallyValid | allocated(v) && v.P())
      ensures Valid()
    {}
  }

  twostate lemma IndependentValidityInductive(v: ExternallyValid, changed: set<ExternallyValid>)
      requires old(AllValid(set v': ExternallyValid | allocated(v') && v'.P()))
      requires forall o :: o !in changed ==> unchanged(o)
      requires forall o :: o in changed ==> o.Valid()
      requires allocated(v)
      decreases v.Repr
      ensures v.Valid()
  {
    assert old(v.Valid());
    forall v': ExternallyValid | v' in v.ValidatableRepr && v' != v && old(allocated(v')) ensures v'.Valid() {
      IndependentValidityInductive(v', changed);
    }
    if v !in changed {
      v.IndependentValidity();
    }
  }

  // This is the "external invariant". It must hold as a precondition and postcondition for
  // every method that crosses the Dafny/external boundary, either incoming or outgoing.
  // It assumes that the Dafny heap cannot be changed in any other way.
  // I have to pass in the set of all objects implementing ExternallyValid since I can't pass in
  // "the Dafny heap".
  predicate AllValid(vs: set<ExternallyValid>) 
    reads vs
    reads set v, o | v in vs && o in v.Repr :: o
  {
    forall v :: v in vs ==> v.Valid()
  }

  // class NotAtomic {

  //   var x: int
  //   var y: int
  //   ghost const Repr: set<object>

  //   constructor(x: int) 
  //     ensures Valid() 
  //     ensures fresh(Repr)
  //   {
  //     this.x := x;
  //     this.y := 2*x;
  //     this.Repr := {this};
  //   }
    
  //   predicate Valid() 
  //     reads this, Repr 
  //     ensures Valid() ==> this in Repr
  //   {
  //     && y == 2*x
  //     && Repr == {this}
  //   }

  //   method Update(x: int) 
  //     requires Valid() // Should follow automatically since this extends ExternallyValid but ¯\_(ツ)_/¯
  //     modifies Repr
  //     ensures Valid()
  //   {
  //     this.x := x;
  //     this.y := 2*x;
  //   }
  // }

  // trait {:extern} ExternalNotAtomic {
  //   // TODO-RS: It may be possible to avoid the duplicate definitions of
  //   // Valid() and Repr if this trait could extend ExternallyValid itself
  //   predicate ExtValid() 
  //     reads this, ExtRepr 
  //     ensures ExtValid() ==> this in ExtRepr
  //   ghost var ExtRepr: set<object>

  //   method Update(x: int)
  //     requires AllValid(set v: ExternallyValid | allocated(v) && v.P())
  //     modifies ExtRepr
  //     ensures AllValid(set v: ExternallyValid | allocated(v) && v.P())
  // }

  // class AsExternalNotAtomic extends ExternalNotAtomic, ExternallyValid {
  //   const wrapped: NotAtomic
  //   predicate Valid() 
  //     reads this, Repr 
  //     ensures Valid() ==> this in Repr
  //     ensures Valid() ==> forall v :: v in ValidatableRepr ==> v.Repr <= Repr
  //     ensures Valid() ==> forall v :: v in ValidatableRepr && v != this ==> this !in v.Repr
  //     ensures Valid() ==> ExtValid()
  //   {
  //     && wrapped in Repr
  //     && Repr == {this} + wrapped.Repr
  //     && wrapped.Valid()
  //     && ExtRepr == Repr
  //     && ExtValid()
  //     && ValidatableRepr == {this}
  //   }

  //   predicate ExtValid() 
  //     reads this, ExtRepr 
  //     ensures ExtValid() ==> this in ExtRepr
  //   {
  //     && wrapped in ExtRepr
  //     && ExtRepr == {this} + wrapped.Repr
  //     && wrapped.Valid()
  //     && ExtRepr == Repr
  //   }

  //   twostate lemma IndependentValidity()
  //     requires old(Valid())
  //     requires unchanged(this)
  //     requires forall v :: v in ValidatableRepr && v != this ==> v.Valid()
  //     ensures Valid()
  //   {}

  //   constructor(wrapped: NotAtomic) 
  //     requires wrapped.Valid() 
  //     ensures Valid() 
  //     ensures fresh(ExtRepr - wrapped.Repr)
  //     ensures forall o: ExternallyValid :: allocated(o) && fresh(o) && o.P() ==> o.Valid()
  //   {
  //     this.wrapped := wrapped;
  //     this.ExtRepr := {this} + wrapped.Repr;
  //     this.Repr := ExtRepr;
  //     this.ValidatableRepr := {this};
  //   }
  //   method Update(x: int) 
  //     requires AllValid(set v: ExternallyValid | allocated(v) && v.P())
  //     modifies ExtRepr
  //     ensures AllValid(set v: ExternallyValid | allocated(v) && v.P())
  //   {
  //     AllValidMakesMeValid();
  //     wrapped.Update(x);
  //     AllStillValid();
  //   }
  // }

  // method MakeExternalNotAtomic() returns (res: AsExternalNotAtomic)
  //   ensures forall o: ExternallyValid :: allocated(o) && fresh(o) && o.P() ==> o.Valid()
  //   ensures res.Valid()
  //   ensures fresh(res.ExtRepr)
  // {
  //   var internal := new NotAtomic(73);
  //   res := new AsExternalNotAtomic(internal);
  // }

  // method SomeOtherExternalMethod() 
  //   requires AllValid(set v: ExternallyValid | allocated(v) && v.P())
  //   ensures AllValid(set v: ExternallyValid | allocated(v) && v.P())
  // {
  //   // Do some external stuff
  // }
}

