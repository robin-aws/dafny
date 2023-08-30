// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0

module A {
  module AA {
    method Main() { print "Main1\n"; }
  }
}

module B {
  class C {
    static method {:main} Main() { print "Main2\n"; }
  }
}

method Main() { print "Main3\n"; }
