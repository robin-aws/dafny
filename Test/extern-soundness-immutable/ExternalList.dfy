include "./List.dfy"

module {:extern "DafnyCollections"} ExternalCollections {

  import opened Collections

  trait {:extern "List"} ExternalList {
    predicate Valid() 

    // TODO-RS: figure out how to enforce that this acts like a function
    function method Length(): uint64 
      requires Valid()
    
    method Get(i: uint64) returns (res: uint64)
      requires Valid()
      ensures Valid()
  }

  type ValidList? = l: List? | l == null || l.Valid()
  type ValidExternalList? = l: ExternalList? | l == null || l.Valid()
  
  /*
   * Adapts a Dafny-internal List as an ExternalList
   */
  class AsExternalList extends ExternalList {

    const wrapped: ValidList?

    constructor(wrapped: List) 
      requires wrapped.Valid()
      ensures Valid()
    {
      this.wrapped := wrapped;
    }

    predicate Valid() 
    {
      && wrapped != null
      && wrapped.Valid()
    }

    function method Length(): uint64
      requires Valid()
    {
      wrapped.Length()
    }
    
    method Get(i: uint64) returns (res: uint64)
    {
      expect wrapped != null;
      expect 0 <= i < wrapped.Length();
      res := wrapped.Get(i);
    }
  }

  /*
   * Adapts an ExternalList as a Dafny-internal List
   */
  class AsList extends List {

    const wrapped: ValidExternalList?

    constructor(wrapped: ExternalList) 
      requires wrapped.Valid()
      ensures Valid()
    {
      this.wrapped := wrapped;
    }

    predicate Valid()
    {
      wrapped != null && wrapped.Valid()
    }

    function method Length(): uint64
      requires Valid()
      ensures Valid()
      ensures |values| < twoToThe64 && Length() == |values| as uint64
    {
      var result := wrapped.Length();

      // TODO-RS: Ideally we would include `expect result >= 0;`, but
      // we can't currently do that in a function, even though we really want that in
      // the compiled version.
      Axiom(|values| < twoToThe64);
      Axiom(result == |values| as uint64);
      result
    }
    
    method Get(i: uint64) returns (res: uint64)
      requires Valid()
      requires 0 <= i < Length()
      ensures Valid()
      ensures Length() == old(Length())
      ensures res == values[i]
    {
      res := wrapped.Get(i);
      
      Axiom(Length() == old(Length()));
      Axiom(res == values[i]);
    }
  }

  // TODO-RS: Replace with `expect {:axiom} ...` when supported.
  lemma {:axiom} Axiom(p: bool) ensures p
}