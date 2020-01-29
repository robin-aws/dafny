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
}