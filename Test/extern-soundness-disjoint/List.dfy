
module {:extern "DafnyCollections"} DafnyCollections {

  trait {:extern} {:termination false} List {
    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    ghost var Repr: set<object>
    ghost var values: seq<nat>

    function method Length(): nat
      requires Valid()
      reads this, Repr
      ensures Length() == |values|
    
    method Get(i: int) returns (res: nat)
      requires Valid()
      requires 0 <= i < Length()
      decreases Repr
      ensures res == values[i]
    
    method Set(i: int, element: nat)
      requires Valid()
      requires 0 <= i < Length()
      decreases Repr
      modifies Repr
      ensures Valid()
      ensures values == old(values[..i]) + [element] + old(values[i + 1..])
      ensures fresh(Repr - old(Repr))
      
    method Add(element: nat)
      requires Valid()
      decreases Repr
      modifies Repr
      ensures Valid()
      ensures values == old(values) + [element]
      ensures fresh(Repr - old(Repr))
  }

  class ArrayList extends List {

    var data: array<nat>
    var length: nat

    constructor() 
      ensures Valid()
      ensures values == []
      ensures fresh(Repr)
    {
      data := new nat[10];
      length := 0;

      values := [];
      Repr := {this, data};
    }

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
    {
      && Repr == {this, data}
      && 0 < data.Length
      && 0 <= length <= data.Length
      && values == data[..length]
    }

    function method Length(): nat
      requires Valid()
      reads this, Repr
      ensures Length() == |values|
    {
      length
    }
    
    method Get(i: int) returns (res: nat)
      requires Valid()
      requires 0 <= i < Length()
      decreases Repr
      ensures res == values[i]
    {
      res := data[i];
    }

    method Set(i: int, element: nat)
      requires Valid()
      requires 0 <= i < Length()
      decreases Repr
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures values == old(values[..i]) + [element] + old(values[i + 1..])
    {
      data[i] := element;

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
      if length == data.Length {
        Grow();
      }
      data[length] := element;
      length := length + 1;

      values := values + [element];
    }

    method Grow() 
      requires Valid()
      modifies Repr
      ensures length < data.Length
      ensures fresh(data)
      ensures unchanged(`length)
      ensures values == old(values)
      ensures Valid()
    {
      var oldSize := data.Length;
      var newData := new nat[2 * data.Length];
      forall i | 0 <= i < oldSize {
        newData[i] := data[i];
      }
      data := newData;
      
      Repr := {this, data};
    }
  }
}