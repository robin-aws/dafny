// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Foo {
  datatype T = T()
}

module Bar {
  datatype T = T()
}

module Consumer {

  import opened Foo
  import opened Bar
  
  export provides Foo, Bar
}