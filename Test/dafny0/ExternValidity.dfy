
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
      requires forall v: Validatable :: v.Valid()
      modifies this
      ensures Valid()
    {
      this.x := newX;
      this.y := 2*x;

      assert forall v: Validatable :: v.Valid();
    }
  }
}

