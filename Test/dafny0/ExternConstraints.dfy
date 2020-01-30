// RUN: %dafny /compile:1 /compileTarget:cs /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:extern "Mod"} Mod1
{
  class MyClass
  {

  }

  class {:extern "classx"} Class1
  {
    method {:extern} method1(obj: MyClass, x: int) requires x >= 0
    
    method {:extern} method2(obj: MyClass, x: int) requires x >= 0
    {
      
    }
    
    method {:extern} method3(obj: MyClass?, x: int)
    {
      if (x >= 0 && obj != null) {
        method2(obj, x);
      }
    }
    
    method {:extern} method4(context: map<object?, string>)
    {

    }

    method {:extern} method5(foo: int)
    {

    }
  }
  
  datatype Result<T> = Success(value: T) | Failure(error: string) {
        predicate method IsFailure() {
            Failure?
        }
        function method PropagateFailure<U>(): Result<U> requires Failure? {
            Failure(this.error)
        }
        function method Extract(): T requires Success? {
            value
        }
    }

  function method RequireWithMessage(b: bool, message: string): (r: Result<()>) 
      ensures r.Success? ==> b 
  {
    if b then Success(()) else Failure(message)
  }

  trait MyTrait {
    method Invert(x: real) returns (y: Result<real>) requires x != 0.0 ensures y.Success? ==> x * y.value == 1.0 decreases *
  }
  
  class MyTraitAdaptor extends MyTrait {

    const wrapped: MyExternTrait

    constructor(wrapped: MyExternTrait) {
      this.wrapped := wrapped;
    }

    method Invert(x: real) returns (y: Result<real>) requires x != 0.0 ensures y.Success? ==> x * y.value == 1.0 decreases * {
      y := wrapped.Invert(x);
      var _ :- RequireWithMessage(y.Success? ==> x * y.value == 1.0, "external implementation failed"); // InternalError
    }
  }
  
  trait {:extern} MyExternTrait {
    method {:extern} Invert(x: real) returns (y: Result<real>) decreases *
  }

  class MyExternTraitAdaptor extends MyExternTrait {

    const wrapped: MyTrait

    constructor(wrapped: MyTrait) {
      this.wrapped := wrapped;
    }

    method {:extern} Invert(x: real) returns (y: Result<real>) decreases * {
      var _ :- RequireWithMessage(x != 0.0, "x cannot be zero"); // IllegalArgumentError
      y := wrapped.Invert(x);
    }
  }
}