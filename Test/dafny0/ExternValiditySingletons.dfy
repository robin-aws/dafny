
module ExternalInvariants {

  trait Validatable {
    ghost const Repr: set<Validatable>
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      ensures Valid() ==> forall v :: v in Repr ==> v in AllValidatables() && v.Repr <= Repr
      ensures Valid() ==> forall v :: v in Repr && v != this ==> this !in v.Repr
    predicate P() {
      true
    }

    twostate lemma AllStillValid() 
      requires old(AllValid())
      requires Valid()
      requires unchanged(AllValidatables())
      requires forall o :: o !in Repr ==> unchanged(o)
      requires forall o :: o in Repr ==> o.Valid()
      ensures AllValid()
    {
      forall v | v in AllValidatables() && old(allocated(v)) ensures v.Valid() {
        IndependentValidityInductive(v, Repr);
      }
    }

    twostate lemma IndependentValidity()
      requires old(Valid())
      requires unchanged(this)
      requires forall v :: v in Repr && v != this ==> v.Valid()
      ensures Valid()
  }

  function AllValidatables(): set<Validatable>

  method {:extern} RegisterExternallyValid(v: Validatable)
    ensures AllValidatables() == old(AllValidatables()) + {v}

  twostate lemma {:axiom} AllValidatablesUnchanged() 
    ensures unchanged(AllValidatables())

  // This is the "external invariant". It must hold as a precondition and postcondition for
  // every method that crosses the Dafny/external boundary, either incoming or outgoing.
  // It assumes that the Dafny heap cannot be changed in any other way.
  // I have to pass in the set of objects implementing Validatable since I can't pass in
  // "the Dafny heap".
  predicate AllValid() 
    reads AllValidatables()
    reads set v, o | v in AllValidatables() && o in v.Repr :: o
  {
    forall v :: v in AllValidatables() ==> v.Valid()
  }

  twostate lemma IndependentValidityInductive(v: Validatable, changed: set<Validatable>)
      requires old(AllValid())
      requires v in AllValidatables()
      requires forall o :: o !in changed ==> unchanged(o)
      requires forall o :: o in changed ==> o.Valid()
      requires allocated(v)
      decreases v.Repr
      ensures v.Valid()
  {
    forall v': Validatable | v' in v.Repr && v' != v && old(allocated(v')) ensures v'.Valid() {
      IndependentValidityInductive(v', changed);
    }
    if v !in changed {
      v.IndependentValidity();
    }
  }

  class NotAtomic extends Validatable {

    var x: int
    var y: int

    constructor(x: int) 
      ensures Valid() 
      ensures fresh(Repr)
      ensures AllValidatables() - old(AllValidatables()) == {this}
    {
      this.x := x;
      this.y := 2*x;
      this.Repr := {this};
      new;
      
      AllValidatablesUnchanged();
      RegisterExternallyValid(this);
    }
    
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      ensures Valid() ==> forall v :: v in Repr ==> v in AllValidatables() && v.Repr <= Repr
      ensures Valid() ==> forall v :: v in Repr && v != this ==> this !in v.Repr
    {
      && y == 2*x
      && Repr == {this}
      && this in AllValidatables()
    }
    twostate lemma IndependentValidity()
      requires old(Valid())
      requires unchanged(this)
      requires forall v :: v in Repr && v != this ==> v.Valid()
      ensures Valid()
    {
    }

    method Update(x: int) 
      requires AllValid()
      requires Valid()
      modifies Repr
      ensures AllValid()
    {
      this.x := x;
      
      // This is not allowed because the external invariant isn't re-established
      // SomeOtherExternalMethod();
      
      // And this fails because `this` is not `Valid()` at this point
      AllValidatablesUnchanged();
      AllStillValid();
      
      this.y := 2*x;

      AllValidatablesUnchanged();
      AllStillValid();
      SomeOtherExternalMethod();
    }
  }

  trait {:extern} ExternalNotAtomic {
    method Update(x: int) 
      requires AllValid()
      modifies this
      ensures AllValid()
  }

  method MakeExternalNotAtomic() returns (res: AsExternalNotAtomic)
    requires AllValid()
    ensures res.Valid()
    ensures fresh(res.Repr)
    ensures AllValid()
  {
    var internal := new NotAtomic(73);
    res := new AsExternalNotAtomic(internal);
  }

  class AsExternalNotAtomic extends Validatable {
    const wrapped: NotAtomic
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      ensures Valid() ==> forall v :: v in Repr ==> v in AllValidatables() && v.Repr <= Repr
      ensures Valid() ==> forall v :: v in Repr && v != this ==> this !in v.Repr
    {
      && wrapped in Repr
      && Repr == {this} + wrapped.Repr
      && wrapped.Valid()
      && Repr <= AllValidatables()
    }

    twostate lemma IndependentValidity()
      requires old(Valid())
      requires unchanged(this)
      requires forall v :: v in Repr && v != this ==> v.Valid()
      ensures Valid()
    {}

    constructor(wrapped: NotAtomic) 
      requires wrapped.Valid() 
      requires wrapped in AllValidatables()
      ensures Valid() 
      ensures fresh(Repr - wrapped.Repr)
    {
      this.wrapped := wrapped;
      this.Repr := {this} + wrapped.Repr;
      new;
      RegisterExternallyValid(this);
    }
    method Update(x: int) 
      requires AllValid()
      requires Valid()
      modifies Repr
      ensures AllValid()
    {
      wrapped.Update(x);
    }
  }


  method SomeOtherExternalMethod() 
    requires AllValid()
    ensures AllValid()
  {
    // Do some external stuff
  }

  method {:main} MyMain() 
    requires AllValid() 
    ensures AllValid() 
  {
    var valid := MakeExternalNotAtomic();
    valid.Update(5);
    SomeOtherExternalMethod();
  }
}

