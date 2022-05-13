// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() {
  foreach x: nat | x == 5 {
    print x;
  }
}