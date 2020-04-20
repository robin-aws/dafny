// RUN: %dafny /compile:3 /compileTarget:cs /print:"%t.print" /dprint:"%t.dprint" "%s" "%S%{dirsep}ExternalConcatList.cs" > "%t"
// RUN: %diff "%s.expect" "%t"
include "./ExternalList.dfy"
include "./Math.dfy"

module ListTest {
  import opened Collections
  import opened Math

  method Main() {
    var list := new SequenceList([1, 2, 3, 4, 5]);
    print "list.Length() = ", list.Length(), "\n";
    
    assert list.Length() == 5;
    var result := list.Get(0);
    print "list.Get(0) = ", result, "\n";
    result := list.Get(2);
    print "list.Get(2) = ", result, "\n";
    result := list.Get(4);
    print "list.Get(4) = ", result, "\n";

    var sum := Sum(list);
    print "Sum(list) = ", sum, "\n";
  }
}