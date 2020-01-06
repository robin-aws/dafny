// RUN: %dafny /compile:1 /compileTarget:cs /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:extern "Mod"} Mod1
{
  class MyClass
  {

  }

  class {:extern "classx"} Class1
  {
    method {:extern "method1"} method1(obj: MyClass, x: int) requires x >= 0
  }
}