
module ExternalInvariants {

  trait Validatable {
    ghost var Repr: set<object>
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
    static predicate AllValid(vs: set<Validatable>) {
      && (forall v :: v in vs ==> v.Valid())
      && (forall v, v' :: (v in vs && v' in vs && v != v') ==> v.Repr !! v'.Repr)
    }
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
      requires Validatable.AllValid(set v: Validatable | true)
      modifies this
      ensures Validatable.AllValid(set v: Validatable | true)
    {
      assert this in set v: Validatable | v.Valid();
      this.x := x;
      this.y := 2*x;
    }
  }

  trait {:extern} ExternalNotAtomic {
    method Update(x: int) 
      requires Validatable.AllValid(set v: Validatable | true)
      modifies this
      ensures Validatable.AllValid(set v: Validatable | true)
  }

  method {:extern} MakeExternalNotAtomic() returns (res: ExternalNotAtomic)
    requires Validatable.AllValid(set v: Validatable | true)
    ensures Validatable.AllValid(set v: Validatable | true)
  {
    var internal := new NotAtomic(73);
    res := new AsExternalNotAtomic(internal);
  }

  method {:extern} MakeExternalNotAtomic_NotValid() returns (res: ExternalNotAtomic)
    requires Validatable.AllValid(set v: Validatable | true)
    ensures Validatable.AllValid(set v: Validatable | true)
  {
    res := new AsExternalNotAtomic.NotValid();
  }

  class AsExternalNotAtomic extends ExternalNotAtomic, Validatable {
    const wrapped: NotAtomic
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
    {
      this in Repr && wrapped.Valid()
    }
    constructor(wrapped: NotAtomic) ensures Valid() {
      this.wrapped := wrapped;
      this.Repr := {this, wrapped} + wrapped.Repr;
    }
    constructor NotValid() {
    }
    method Update(x: int) 
      requires Validatable.AllValid(set v: Validatable | true)
      modifies this
      ensures Validatable.AllValid(set v: Validatable | true)
    {
      wrapped.Update(x);
    }
  }

  class Rational extends Validatable {

    var a: int
    var b: int

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
    {
      && 0 <= a
      && 0 < b
      && this in Repr
    }

    method Invert() 
      requires Valid()
      requires a != 0
      modifies this
      ensures Valid()
    {
      var tmp := a;
      a := b;
      b := tmp;
    }
  }
}

