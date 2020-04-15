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
    decreases Repr
    ensures res == values[i]
  
  method Set(i: int, element: int)
    requires Valid()
    requires 0 <= i < Length()
    decreases Repr
    modifies Repr
    ensures Valid()
    ensures values == old(values[..i]) + [element] + old(values[i + 1..])
    ensures fresh(Repr - old(Repr))
    
  method Add(element: int)
    requires Valid()
    decreases Repr
    modifies Repr
    ensures Valid()
    ensures values == old(values) + [element]
    ensures fresh(Repr - old(Repr))
}

class ArrayList extends List {

  var data: array<int>
  var length: int

  constructor() 
    ensures Valid()
    ensures values == []
  {
    data := new int[10];
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
    decreases Repr
    ensures res == values[i]
  {
    res := data[i];
  }

  method Set(i: int, element: int)
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

  method Add(element: int)
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
    var newData := new int[2 * data.Length];
    forall i | 0 <= i < oldSize {
      newData[i] := data[i];
    }
    data := newData;
    
    Repr := {this, data};
  }
}

trait {:extern} ExternalList {

  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  ghost var Repr: set<object>

  function method Length(): int 
    requires Valid()
    reads Repr
    ensures Valid()
  
  method Get(i: int) returns (res: int)
    requires Valid()
    decreases Repr
  
  method Set(i: int, element: int)
    requires Valid()
    modifies Repr
    decreases Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
  
  method Add(element: int)
    requires Valid()
    modifies Repr
    decreases Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
}

class AsExternalList extends ExternalList {

  var wrapped: List

  constructor(wrapped: List) 
    requires wrapped.Valid()
    ensures Valid()
  {
    this.wrapped := wrapped;
    this.Repr := {this} + wrapped.Repr;
  }

  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr 
  {
    && wrapped in Repr
    && Repr == {this} + wrapped.Repr
    && wrapped in wrapped.Repr
    && this !in wrapped.Repr
    && wrapped.Repr <= Repr
    && wrapped.Valid()
  }

  function method Length(): int 
    requires Valid()
    reads Repr
  {
    wrapped.Length()
  }
  
  method Get(i: int) returns (res: int)
    requires Valid()
    decreases Repr
  {
    expect 0 <= i < Length();
    res := wrapped.Get(i);
  }
  
  method Set(i: int, element: int)
    requires Valid()
    modifies Repr
    decreases Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
  {
    expect 0 <= i < Length();
    wrapped.Set(i, element);
    Repr := {this} + wrapped.Repr;
  }
  
  method Add(element: int)
    requires Valid()
    modifies Repr
    decreases Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
  {
    wrapped.Add(element);
    Repr := {this} + wrapped.Repr;
  }
}

class AsList extends List {

  var wrapped: ExternalList

  constructor(wrapped: ExternalList) 
    requires wrapped.Valid()
    ensures Valid()
  {
    this.wrapped := wrapped;
    this.Repr := {this} + wrapped.Repr;
  }

  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr 
  {
    && wrapped in Repr
    && Repr == {this} + wrapped.Repr
    && wrapped in wrapped.Repr
    && this !in wrapped.Repr
    && wrapped.Repr <= Repr
    && wrapped.Valid()
  }

  function method Length(): int
    requires Valid()
    reads this, Repr
    ensures Length() == |values|
  {
    assume {:axiom} wrapped.Length() == |values|;
    wrapped.Length()
  }
  
  method Get(i: int) returns (res: int)
    requires Valid()
    requires 0 <= i < Length()
    decreases Repr
    ensures res == values[i]
  {
    res := wrapped.Get(i);
    assume {:axiom} res == values[i];
  }
  
  method Set(i: int, element: int)
    requires Valid()
    requires 0 <= i < Length()
    decreases Repr
    modifies Repr
    ensures Valid()
    ensures values == old(values[..i]) + [element] + old(values[i + 1..])
    ensures fresh(Repr - old(Repr))
  {
    wrapped.Set(i, element);

    // Presumably cheap sanity check
    var elementAfter := wrapped.Get(i);
    expect elementAfter == element;

    values := values[..i] + [element] + values[i + 1..];
    Repr := {this} + wrapped.Repr;
  }

  method Add(element: int)
    requires Valid()
    decreases Repr
    modifies Repr
    ensures Valid()
    ensures values == old(values) + [element]
    ensures fresh(Repr - old(Repr))
  {
    var lengthBefore := Length();

    wrapped.Add(element);

    values := values + [element];
    Repr := {this} + wrapped.Repr;

    expect Length() == lengthBefore + 1;
  }
}