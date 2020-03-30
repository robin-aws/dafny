
module ExternalInvariants {

  trait Validatable {
    ghost var Repr: set<object>
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr

  }

  class NotAtomic extends Validatable {

    var x: int
    var y: int

    constructor(x: int) ensures Valid() {
      this.x := x;
      this.y := 2*x;
      this.Repr := {this};
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
    {
      && y == 2*x
      && this in Repr
    }

    method Update(newX: int) 
      requires Valid()
      requires 
        var validatables: set<Validatable> := set y: Validatable | true;
        forall v :: v in validatables ==> v.Valid()
      modifies this
      ensures Valid()
    {
      this.x := newX;
      ghost var validatables: set<Validatable> := set y: Validatable | true;
      this.y := 2*x;
      assert forall v :: v in validatables ==> v.Valid();
    }
  }
}