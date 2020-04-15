trait List {
  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  ghost var Repr: set<object>

  ghost var values: seq<int>

  function method Length(): int
    requires Valid()
    reads this, Repr
    ensures Length() == |values|
  
  method Get(i: int) returns (res: int)
    requires Valid()
    requires 0 <= i < Length()
    ensures res == values[i]
  
  method Set(i: int, element: int)
    requires Valid()
    requires 0 <= i < Length()
    modifies Repr
    ensures values == old(values[..i]) + [element] + old(values[i + 1..])
  
  method Add(element: int)
    requires Valid()
    modifies Repr
    ensures values == old(values) + [element]
}

class ArrayList extends List {

  var data: array<int>
  var length: int

  constructor() {
    data := new int[10];
    length := 0;
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

  function method Length(): int
    requires Valid()
    reads this, Repr
    ensures Length() == |values|
  {
    length
  }
  
  method Get(i: int) returns (res: int)
    requires Valid()
    requires 0 <= i < Length()
    ensures res == values[i]
  {
    res := data[i];
  }

  method Set(i: int, element: int)
    requires Valid()
    requires 0 <= i < Length()
    modifies Repr
    ensures values == old(values[..i]) + [element] + old(values[i + 1..])
  {
    data[i] := element;
  }

  method Add(element: int)
    requires Valid()
    modifies Repr
    ensures values == old(values) + [element]
  {
    if length == data.Length {
      Grow();
    }
    data[length] := element;
    length := length + 1;
  }

  method Grow() 
    requires Valid()
    modifies this`data, data
    ensures length < data.Length
    ensures fresh(data)
  {
    var oldSize := data.Length;
    var newData := new int[2 * data.Length];
    forall i | 0 <= i < oldSize {
      newData[i] := data[i];
    }
    data := newData;
  }
}