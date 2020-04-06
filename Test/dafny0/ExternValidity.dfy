
module ExternalInvariants {

  trait Validatable {
    ghost var Repr: set<object>
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
  }

  // This is the "external invariant". It must hold as a precondition and postcondition for
  // every method that crosses the Dafny/external boundary, either incoming or outgoing.
  // It assumes that the Dafny heap cannot be changed in any other way.
  // I have to pass in the set of objects implementing Validatable since I can't pass in
  // "the Dafny heap".
  predicate AllValid(vs: set<Validatable>) reads vs, UnionAll(set v | v in vs :: v.Repr) {
    && (forall v :: v in vs ==> v.Valid())
    && (forall v, v' :: (v in vs && v' in vs && v != v') ==> v.Repr !! v'.Repr)
  }

  function UnionAll<T>(sets: set<set<T>>): set<T> {
    set o,s | s in sets && o in s :: o
  }
 
  class NotAtomic extends Validatable {

    var x: int
    var y: int

    constructor(x: int) ensures Valid() {
      this.x := x;
      this.y := 2*x;
      this.Repr := {this};
    }
    constructor NotValid() {
    }
    
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
    {
      && y == 2*x
      && this in Repr
    }

    method Update(x: int) 
      requires AllValid(set v: Validatable | true)
      requires Valid() // Should follow automatically since this extends Validatable but ¯\_(ツ)_/¯
      modifies Repr
      ensures AllValid(set v: Validatable | true)
    {
      this.x := x;
      // This fails because `this` is not `Valid()` at this point. Yay!
      // SomeOtherExternalMethod();
      this.y := 2*x;
      SomeOtherExternalMethod();
    }
  }

  trait {:extern} ExternalNotAtomic {
    method Update(x: int) 
      requires AllValid(set v: Validatable | true)
      modifies this
      ensures AllValid(set v: Validatable | true)
  }

  method MakeExternalNotAtomic() returns (res: Validatable)
    requires AllValid(set v: Validatable | true)
    ensures AllValid(set v: Validatable | true)
  {
    var internal := new NotAtomic(73);
    res := new AsExternalNotAtomic(internal);
    // Postcondition doesn't hold. I probably need to assert that the constructors
    // don't instantiate any new Validatables. 
  }

  class AsExternalNotAtomic extends Validatable {
    const wrapped: NotAtomic
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && wrapped in Repr
      && wrapped.Repr <= Repr
      && this !in wrapped.Repr
      && wrapped.Valid()
    }
    constructor(wrapped: NotAtomic) 
      requires wrapped.Valid() 
      ensures Valid() 
    {
      this.wrapped := wrapped;
      this.Repr := {this} + wrapped.Repr;
    }
    method Update(x: int) 
      requires AllValid(set v: Validatable | true)
      requires Valid()
      modifies Repr
      ensures AllValid(set v: Validatable | true)
    {
      wrapped.Update(x);
    }
  }

  method SomeOtherExternalMethod() 
    requires AllValid(set v: Validatable | true)
    ensures AllValid(set v: Validatable | true)
  {
    // Do some external stuff
  }

  method Main() {
    // Precondition doesn't hold. How do I convince Dafny that no instances of ANY
    // reference types exist yet?
    var valid := MakeExternalNotAtomic();
  }
}

