// RUN: %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module StaticMembers {
  trait Tr {
    // the following static members must also be given bodies, but that's checked by the compiler
    static function method Func(): int
    static method Method()
    static twostate function TwoF(): int
    static twostate lemma TwoL()
    static inductive predicate P()
    static copredicate Q()
    static inductive lemma IL()
    static colemma CL()
  }
}
