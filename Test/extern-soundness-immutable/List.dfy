
module Collections {

  const twoToThe8 := 0x1_00
  newtype {:nativeType "byte"} uint8 = x | 0 <= x < 0x1_00
  const twoToThe64 := 0x1_0000_0000_0000_0000
  newtype {:nativeType "ulong"} uint64 = x | 0 <= x < 0x1_0000_0000_0000_0000

  trait {:termination false} List {
    predicate Valid()
      ensures Valid() ==> |values| < twoToThe64

    ghost const values: seq<uint8>

    function method Length(): uint64
      requires Valid()
      ensures Length() == |values| as uint64
    
    method Get(i: uint64) returns (res: uint8)
      requires Valid()
      requires 0 <= i < Length()
      ensures res == values[i]
  }

  class SequenceList extends List {

    const data: seq<uint8>

    constructor(s: seq<uint8>) 
      requires |s| < twoToThe64
      ensures Valid()
      ensures Length() == |s| as uint64
    {
      data := s;
      values := s;
    }

    predicate Valid() 
      ensures Valid() ==> |values| < twoToThe64
    {
      && data == values 
      && |values| < twoToThe64
    }

    function method Length(): uint64
      requires Valid()
      ensures Length() == |values| as uint64
    {
      |data| as uint64
    }
    
    method Get(i: uint64) returns (res: uint8)
      requires Valid()
      requires 0 <= i < Length()
      ensures res == values[i]
    {
      res := data[i];
    }
  }

  // This doesn't work because you can't prove termination 
  // in the presence of recursive calls but no Repr

  // class ConcatList extends List {

  //   const left: List
  //   const right: List

  //   constructor(left: List, right: List) 
  //     requires left.Valid()
  //     requires right.Valid()
  //     ensures Valid()
  //   {
  //     this.left := left;
  //     this.right := right;
  //     values := left.values + right.values;
  //     Repr := {this} + left.Repr + right.Repr;
  //   }

  //   predicate Valid() 
  //     ensures Valid() ==> |values| < twoToThe64
  //   {
  //     && left in Repr
  //     && this !in left.Repr
  //     && left.Repr <= Repr
  //     && left.Valid() 
  //     && right in Repr
  //     && right.Valid()
  //   }

  //   function method Length(): uint64
  //     requires Valid()
  //     reads Repr
  //     ensures Length() == |values| as uint64
  //   {
  //     left.Length() + right.Length()
  //   }
    
  //   method Get(i: uint64) returns (res: uint64)
  //     requires Valid()
  //     requires 0 <= i < Length()
  //     decreases Repr 
  //     ensures res == values[i]
  //   {
  //     if i < left.Length() {
  //       res := left.Get(i);
  //     } else {
  //       res := right.Get(i);
  //     }
  //   }
  // }
}