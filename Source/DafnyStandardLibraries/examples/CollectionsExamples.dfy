/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module CollectionsExamples {

  // These examples focus mainly on execution testing coverage,
  // but they also use AssertAndExpect to prove some of the simpler cases as well.
  // If and when we have some way of measuring "specification coverage",
  // this pattern should help with that kind of coverage as well.
  //
  // There are lots of small test methods here,
  // which besides following the general best practice
  // of testing one or perhaps a couple of related things at once,
  // helps to keep the verification cost from running away too much.

  module SeqExamples {

    import opened DafnyStdLibs.Wrappers
    import opened DafnyStdLibs.Collections.Seqs
    import opened Helpers

    // A sequence that's long enough to be non-trivial
    // but short enough to support lots of verification of results.
    const s := [1, 1, 2, 3, 5, 8, 13, 21]

    method {:test} TestSequenceBasics() {
      AssertAndExpect(First(s) == 1);
      AssertAndExpect(DropFirst(s) == [1, 2, 3, 5, 8, 13, 21]);
      AssertAndExpect(Last(s) == 21);
      AssertAndExpect(DropLast(s) == [1, 1, 2, 3, 5, 8, 13]);

      var asArray := ToArray(s);
      AssertAndExpect(asArray[..] == s);
      AssertAndExpect(reveal ToSet(); ToSet(s[1..]) == {1, 2, 3, 5, 8, 13, 21});
    }

    method {:test} TestSequenceIndexOf() {
      AssertAndExpect(IndexOf(s, 5) == 4);
      expect IndexOf(s, 1) == 0;
      AssertAndExpect(IndexOfOption(s, 5) == Some(4));
      AssertAndExpect(IndexOfOption(s, 42) == None);
    }

    method {:test} TestSequenceLastIndexOf() {
      AssertAndExpect(LastIndexOf(s, 5) == 4);
      expect LastIndexOf(s, 1) == 1;
      AssertAndExpect(LastIndexOfOption(s, 5) == Some(4));
      AssertAndExpect(LastIndexOfOption(s, 42) == None);
    }

    method {:test} TestSequenceAddOrRemove() {
      expect Insert(s, 42, 1) == [1, 42, 1, 2, 3, 5, 8, 13, 21];
      expect Remove(s, 5) == [1, 1, 2, 3, 5, 13, 21];
      expect RemoveValue(s, 5) == [1, 1, 2, 3, 8, 13, 21];
      expect RemoveValue(s, 42) == [1, 1, 2, 3, 5, 8, 13, 21];
    }

    method {:test} TestRepeat() {
      AssertAndExpect(Repeat(42, 5) == [42, 42, 42, 42, 42]);
    }

    method {:test} TestReverse() {
      AssertAndExpect(Reverse(s) == [21, 13, 8, 5, 3, 2, 1, 1]);
    }

    method {:test} TestZipping() {
      AssertAndExpect(Zip([1, 2, 3], [4, 5, 6]) == [(1, 4), (2, 5), (3, 6)]);
      AssertAndExpect(Unzip([(1, 4), (2, 5), (3, 6)]) == ([1, 2, 3], [4, 5, 6]));
    }

    method {:test} TestMaxMin() {
      expect Max(s) == 21;
      expect Min(s) == 1;
    }

    method {:test} TestFlatten() {
      AssertAndExpect(Flatten([[1, 1, 2], [3, 5], [], [8, 13, 21]]) == s);
      AssertAndExpect(FlattenReverse([[1, 1, 2], [3, 5], [], [8, 13, 21]]) == s);
    }

    method {:test} TestMapFilter() {
      AssertAndExpect(Map(x => x * 2, s) == [2, 2, 4, 6, 10, 16, 26, 42]);

      var failIfThirteen := x => if x != 13 then Success(x + 2) else Failure("I said NOT thirteen");
      expect MapWithResult(failIfThirteen, [1, 2, 3]) == Success([3, 4, 5]);
      expect MapWithResult(failIfThirteen, s) == Failure("I said NOT thirteen");

      expect Filter(x => x % 2 == 0, s) == [2, 8];
    }

    method {:test} TestFolding() {
      expect FoldLeft((x, y) => x + y, 0, s) == 54;
      expect FoldLeft((x, y) => x + [y], [], s) == s;

      expect FoldRight((x, y) => x + y, s, 0) == 54;
      expect FoldRight((x, y) => [x] + y, [], s) == s;
    }

    method {:test} TestSetToSeq() {
      var mySet := {4, 1, 56, -6};
      var asSeq := SetToSeq(mySet);
      var backToSet := ToSet(asSeq);
      expect backToSet == mySet;
    }

    method {:test} TestSorting() {
      expect MergeSortBy((x, y) => x <= y, Reverse(s)) == s;

      var asSet := ToSet(s);
      var asSortedSeq := SetToSortedSeq(asSet, (x, y) => x <= y);
      expect asSortedSeq == [1, 2, 3, 5, 8, 13, 21];
    }
  }

  module SetExamples {

    import opened DafnyStdLibs.Wrappers
    import opened DafnyStdLibs.Collections.Sets
    import opened Helpers

    method {:test} TestSetRange() {
      expect SetRange(5, 10) == {5, 6, 7, 8, 9};
      expect SetRangeZeroBound(5) == {0, 1, 2, 3, 4};
    }

    method {:test} TestExtractFromSingleton() {
      AssertAndExpect(ExtractFromSingleton({42}) == 42);
    }

    method {:test} TestMapFilter() {
      expect Map(x => x + 2, {1, 2, 3}) == {3, 4, 5};
      expect Filter(x => x % 2 == 0, {1, 2, 3, 4, 5}) == {2, 4};
    }
  }

  module MapsExamples {

    import opened DafnyStdLibs.Wrappers
    import opened DafnyStdLibs.Collections.Maps
    import opened Helpers

    const m := map[1 := 10, 2 := 20, 3 := 30]

    method {:test} TestBasics() {
      AssertAndExpect(Get(m, 2) == Some(20));
      AssertAndExpect(Get(m, 42) == None);

      expect ToImap(m) == imap[1 := 10, 2 := 20, 3 := 30];
    }

    method {:test} TestOperations() {
      expect Remove(m, 2) == map[1 := 10, 3 := 30];
      expect RemoveKeys(m, {1, 3}) == map[2 := 20];
      expect Restrict(m, {1, 3}) == map[1 := 10, 3 := 30];
      expect Union(m, map[3 := 300, 4 := 400]) == map[1 := 10, 2 := 20, 3 := 300, 4 := 400];
    }
  }

  module ImapsExamples {

    import opened DafnyStdLibs.Wrappers
    import opened DafnyStdLibs.Collections.Imaps
    import opened Helpers

    const m := imap[1 := 10, 2 := 20, 3 := 30]

    method {:test} TestBasics() {
      AssertAndExpect(Get(m, 2) == Some(20));
      AssertAndExpect(Get(m, 42) == None);
    }
  }


  module ArraysExamples {

    import opened DafnyStdLibs.Wrappers
    import opened DafnyStdLibs.Relations
    import opened DafnyStdLibs.Collections.Arrays
    import opened Helpers

    method {:test} TestBinarySearch() {
      var a := new int[] [1, 1, 2, 3, 5, 8, 13, 21];
      var lessThan := (x, y) => x < y;

      var r := BinarySearch(a, 8, lessThan);
      expect r == Some(5);

      r := BinarySearch(a, 0, lessThan);
      expect r == None;

      r := BinarySearch(a, 22, lessThan);
      expect r == None;
    }
  }

}
