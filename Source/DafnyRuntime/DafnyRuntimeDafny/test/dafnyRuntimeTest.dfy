
include "../src/dafnyRuntime.dfy"

abstract module DafnyRuntimeTest {

    import opened D: Dafny

    method {:test} HappyPath() {
        EnsureSizeTLimitAboveMinimum();
        var a := NativeArray<int>.Make(5);
        for i: size_t := 0 to 5 
            invariant a.Valid()
        {
            a.Update(i, i as int);
        }
        var frozen := a.Freeze(a.Length());
        var s: Sequence<int> := new ArraySequence(frozen);
        for i: size_t := 0 to 5 
            invariant a.Valid()
        {
            var x := s.Select(i);
            expect x == i as int;
        }
    }
}