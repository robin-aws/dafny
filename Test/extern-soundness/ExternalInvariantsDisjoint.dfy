
module ExternalInvariants {

  trait {:termination false} ExternallyValid {
    ghost const Repr: set<object>
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> 
        && this in Repr
    
    // Dummy predicate to avoid "/!\ No terms found to trigger on." warning
    predicate P() {
      true
    }

    // Slightly silly lemma that might go away if we tweak Dafny's heuristics a bit
    lemma AllValidMakesMeValid() 
      requires AllValid(set v: ExternallyValid | allocated(v) && v.P())
      ensures Valid()
    {}
  }

  predicate AllValid(vs: set<ExternallyValid>) 
    reads vs
    reads set v, o | v in vs && o in v.Repr :: o
  {
    forall v :: v in vs ==> v.Valid() && forall v, v' :: v in vs && v' in vs - {v} ==> v.Repr !! v'.Repr
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

