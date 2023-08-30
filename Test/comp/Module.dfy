// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0

// Simple sanity test of nested modules
module Parent {
  module Child {
    method Test() {
      print "hi from a nested module\n";
    }
  }
}

method Main() {
  Parent.Child.Test();
}
