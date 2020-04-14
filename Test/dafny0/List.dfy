class ArrayList<T(0)> {

  var data: array<T>
  var count: int

  constructor() {
    data := new T[10];
    count := 0;
  }

  predicate Valid() reads this {
    && 0 < data.Length
    && 0 <= count <= data.Length
  }

  method Add(t: T) 
    requires Valid()
    modifies this, data
  {
    if count == data.Length {
      Grow();
    }
    data[count] := t;
    count := count + 1;
  }

  method Grow() 
    requires Valid()
    modifies this`data, data
    ensures count < data.Length
    ensures fresh(data)
  {
    var oldSize := data.Length;
    var newData := new T[2 * data.Length];
    forall i | 0 <= i < oldSize {
      newData[i] := data[i];
    }
    data := newData;
  }
}