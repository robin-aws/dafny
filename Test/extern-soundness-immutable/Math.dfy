include "./ExternalList.dfy"

module Math {

  import opened Collections
  
  method Sum(list: List) returns (res: int) 
    requires list.Valid()
  {
    res := 0;
    var i := 0;
    var n := list.Length();
    while i < n {
      var element := list.Get(i);
      res := res + element as int;
      i := i + 1;
    }
  }
}

module {:extern "DafnyMath"} MathExtern {
  import Math
  import opened Collections
  import opened ExternalCollections

  // Exposed method for external client
  method ExternalSum(list: ExternalList) returns (res: uint64)
    requires list.Valid()
  {
    var asList := new AsList(list);
    var result := Math.Sum(asList);
    expect 0 <= result < twoToThe64;
    res := result as uint64;
  }
}
