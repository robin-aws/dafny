// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate P() {
  forall m:mode :: m == m
}
