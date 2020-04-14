
module ExternalInvariants {

  trait Validatable {
    ghost const Repr: set<Validatable>
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      ensures Valid() ==> forall v :: v in Repr ==> v.Repr <= Repr
      ensures Valid() ==> forall v :: v in Repr && v != this ==> this !in v.Repr
    predicate P() {
      true
    }

    twostate lemma AllStillValid() 
      requires old(AllValid(set v: Validatable | allocated(v) && v.P()))
      requires Valid()
      requires forall o :: o !in Repr ==> unchanged(o)
      requires forall o :: o in Repr ==> o.Valid()
      ensures AllValid(set v: Validatable | allocated(v) && v.P())
    {
      forall v: Validatable | old(allocated(v)) && v.P() ensures v.Valid() {
        IndependentValidityInductive(v, Repr);
      }
    }

    twostate lemma IndependentValidity()
      requires old(Valid())
      requires unchanged(this)
      requires forall v :: v in Repr && v != this ==> v.Valid()
      ensures Valid()
  }

  // This is the "external invariant". It must hold as a precondition and postcondition for
  // every method that crosses the Dafny/external boundary, either incoming or outgoing.
  // It assumes that the Dafny heap cannot be changed in any other way.
  // I have to pass in the set of objects implementing Validatable since I can't pass in
  // "the Dafny heap".
  predicate AllValid(vs: set<Validatable>) 
    reads vs
    reads set v, o | v in vs && o in v.Repr :: o
  {
    forall v :: v in vs ==> v.Valid()
  }

  twostate lemma IndependentValidityInductive(v: Validatable, changed: set<Validatable>)
      requires old(AllValid(set v': Validatable | allocated(v') && v'.P()))
      requires forall o :: o !in changed ==> unchanged(o)
      requires forall o :: o in changed ==> o.Valid()
      requires allocated(v)
      decreases v.Repr
      ensures v.Valid()
  {
    assert old(v.Valid());
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
      ensures forall o: Validatable :: allocated(o) && fresh(o) && o.P() ==> o.Valid()
      ensures fresh(Repr)
    {
      this.x := x;
      this.y := 2*x;
      this.Repr := {this};
    }
    
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      ensures Valid() ==> forall v :: v in Repr ==> v.Repr <= Repr
      ensures Valid() ==> forall v :: v in Repr && v != this ==> this !in v.Repr
    {
      && y == 2*x
      && Repr == {this}
    }
    twostate lemma IndependentValidity()
      requires old(Valid())
      requires unchanged(this)
      requires forall v :: v in Repr && v != this ==> v.Valid()
      ensures Valid()
    {
    }

    method Update(x: int) 
      requires AllValid(set v: Validatable | allocated(v) && v.P())
      requires Valid() // Should follow automatically since this extends Validatable but ¯\_(ツ)_/¯
      modifies Repr
      ensures AllValid(set v: Validatable | allocated(v) && v.P())
    {
      this.x := x;
      
      // This is not allowed because the external invariant isn't re-established
      // SomeOtherExternalMethod();
      
      // And this fails because `this` is not `Valid()` at this point
      // AllStillValid();
      
      this.y := 2*x;

      AllStillValid();
      SomeOtherExternalMethod();
    }
  }

  trait {:extern} ExternalNotAtomic {
    method Update(x: int) 
      requires AllValid(set v: Validatable | v.P())
      modifies this
      ensures AllValid(set v: Validatable | v.P())
  }

  method MakeExternalNotAtomic() returns (res: AsExternalNotAtomic)
    ensures forall o: Validatable :: allocated(o) && fresh(o) && o.P() ==> o.Valid()
    ensures res.Valid()
    ensures fresh(res.Repr)
  {
    var internal := new NotAtomic(73);
    res := new AsExternalNotAtomic(internal);
  }

  class AsExternalNotAtomic extends Validatable {
    const wrapped: NotAtomic
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      ensures Valid() ==> forall v :: v in Repr ==> v.Repr <= Repr
      ensures Valid() ==> forall v :: v in Repr && v != this ==> this !in v.Repr
    {
      && wrapped in Repr
      && Repr == {this} + wrapped.Repr
      && wrapped.Valid()
    }

    twostate lemma IndependentValidity()
      requires old(Valid())
      requires unchanged(this)
      requires forall v :: v in Repr && v != this ==> v.Valid()
      ensures Valid()
    {

    }

    constructor(wrapped: NotAtomic) 
      requires wrapped.Valid() 
      ensures forall o: Validatable :: allocated(o) && fresh(o) && o.P() ==> o.Valid()
      ensures Valid() 
      ensures fresh(Repr - wrapped.Repr)
    {
      this.wrapped := wrapped;
      this.Repr := {this} + wrapped.Repr;
    }
    method Update(x: int) 
      requires AllValid(set v: Validatable | allocated(v) && v.P())
      requires Valid()
      modifies Repr
      ensures AllValid(set v: Validatable | allocated(v) && v.P())
    {
      wrapped.Update(x);
    }
  }


  method SomeOtherExternalMethod() 
    requires AllValid(set v: Validatable | allocated(v) && v.P())
    ensures AllValid(set v: Validatable | allocated(v) && v.P())
  {
    // Do some external stuff
  }

  method {:main} MyMain() 
    requires AllValid(set v: Validatable | allocated(v) && v.P()) 
    ensures AllValid(set v: Validatable | allocated(v) && v.P()) 
  {
    var valid := MakeExternalNotAtomic();
    valid.Update(5);
    SomeOtherExternalMethod();
  }
}

