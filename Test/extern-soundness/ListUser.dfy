include "./ExternalList.dfy"

module ListUser {

  import opened Collections
  import opened ExternalCollections

  method Sum(list: List) returns (res: nat) 
    requires list.Valid()
  {
    res := 0;
    var i := 0;
    var n := list.Length();
    while i < n {
      var element := list.Get(i);
      res := res + element;
      i := i + 1;
    }
  }

  method ExternalSum(list: ExternalList) returns (res: nat) 
    requires list.Valid()
  {
    var asList := new AsList(list);
    res := Sum(asList);
  }
}
