
module Std.Aggregators {

  import opened Actions
  import opened Wrappers
  import opened DynamicArray
  import Collections.Seq

  trait Accumulator<T> extends Action<T, ()>, ConsumesAllProof<T, ()> {

    ghost function Action(): Action<T, ()> {
      this
    }

    // For better readability
    method Accept(t: T)
      requires Valid()
      reads Reads(t)
      modifies Modifies(t)
      ensures Ensures(t, ())
    {
      CanConsumeAll(history, t);
      var r := Invoke(t);
      assert r == ();
    }
  }

  class ArrayAggregator<T> extends Accumulator<T> {

    var storage: DynamicArray<T>

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && storage in Repr
      && this !in storage.Repr
      && storage.Repr <= Repr
      && storage.Valid?()
      && Consumed() == storage.items
    }

    constructor() 
      ensures Valid()
      ensures fresh(Repr - {this})
      ensures history == []
    {
      var a := new DynamicArray();

      history := [];
      height := 1;
      Repr := {this} + {a} + a.Repr;
      this.storage := a;
    }

    ghost predicate CanConsume(history: seq<(T, ())>, next: T)
      decreases height
    {
      true
    }
    ghost predicate CanProduce(history: seq<(T, ())>)
      decreases height
    {
      true
    }

    method Invoke(t: T) returns (r: ()) 
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      assert Consumed() == storage.items;
      storage.Push(t);

      r := ();
      Update(t, r);
      Repr := {this} + {storage} + storage.Repr;
      assert Consumed() == old(Consumed()) + [t];
      assert Valid();
    }

    method RepeatUntil(t: T, stop: (()) -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<T, ()>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Consumed() :: i == t
      reads Reads(t)
      modifies Repr
      decreases Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop, eventuallyStopsProof);
    }

    lemma CanConsumeAll(history: seq<(T, ())>, next: T) 
      requires Action().CanProduce(history)
      ensures Action().CanConsume(history, next) 
    {}
  }

  class Folder<T, R> extends Accumulator<T> {

    ghost const init: R
    const f: (R, T) -> R
    var value: R

    constructor(init: R, f: (R, T) -> R) 
      ensures Valid()
      ensures fresh(Repr)
    {
      this.init := init;
      this.f := f;
      this.value := init;
      this.Repr := {this};
      this.history := [];
      new;
      reveal Seq.FoldLeft();
      assert value == Seq.FoldLeft(f, init, Consumed());
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && value == Seq.FoldLeft(f, init, Consumed())
    }

    ghost predicate CanConsume(history: seq<(T, ())>, next: T)
      decreases height
    {
      true
    }
    ghost predicate CanProduce(history: seq<(T, ())>)
      decreases height
    {
      true
    }

    method Invoke(t: T) returns (r: ()) 
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      value := f(value, t);
      r := ();
      Update(t, ());

      assert old(value) == Seq.FoldLeft(f, init, old(Consumed()));
      assert Consumed() == old(Consumed()) + [t];
      reveal Seq.FoldLeft();
      Seq.FoldLeftNewRightElement(f, init, old(Consumed()), t);
      assert value == Seq.FoldLeft(f, init, Consumed());
      assert Valid();
    }

    method RepeatUntil(t: T, stop: (()) -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<T, ()>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Consumed() :: i == t
      reads Reads(t)
      modifies Repr
      decreases Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop, eventuallyStopsProof);
    }

    lemma CanConsumeAll(history: seq<(T, ())>, next: T) 
      requires Action().CanProduce(history)
      ensures Action().CanConsume(history, next) 
    {}
  }

  // TODO: This is also a Folder([], (x, y) => x + [y])
  class Collector<T> extends Accumulator<T> {

    var values: seq<T>

    constructor() 
      ensures Valid()
      ensures fresh(Repr)
    {
      values := [];
      history := [];
      Repr := {this};
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      this in Repr 
    }

    ghost predicate CanConsume(history: seq<(T, ())>, next: T)
      requires CanProduce(history)
      decreases height
    {
      true
    }

    ghost predicate CanProduce(history: seq<(T, ())>)
      decreases height
    {
      true
    }

    method {:verify false} Invoke(t: T) returns (nothing: ()) {
      values := values + [t];
    }

    method RepeatUntil(t: T, stop: (()) -> bool, ghost eventuallyStopsProof: ProducesTerminatedProof<T, ()>)
      requires Valid()
      requires eventuallyStopsProof.Action() == this
      requires eventuallyStopsProof.FixedInput() == t
      requires eventuallyStopsProof.StopFn() == stop
      requires forall i <- Consumed() :: i == t
      reads Reads(t)
      modifies Repr
      decreases Repr
      ensures Valid()
    {
      DefaultRepeatUntil(this, t, stop, eventuallyStopsProof);
    }

    method Pop() returns (t: T) 
      requires Valid()
      requires 0 < |values|
      reads Repr
      modifies Repr
      ensures Valid()
    {
      t := values[0];
      values := values[1..];
    }

    lemma CanConsumeAll(history: seq<(T, ())>, next: T) 
      requires Action().CanProduce(history)
      ensures Action().CanConsume(history, next) 
    {}
  }

  method {:rlimit 0} AggregatorExample() {
    var a: ArrayAggregator<nat> := new ArrayAggregator();
    var _ := a.Invoke(1);
    var _ := a.Invoke(2);
    var _ := a.Invoke(3);
    var _ := a.Invoke(4);
    var _ := a.Invoke(5);
    var _ := a.Invoke(6);
    assert a.Consumed() == [1, 2, 3, 4, 5, 6];
    assert a.storage.items == [1, 2, 3, 4, 5, 6];
  }
}