module ArithmeticExamples {
  import opened DafnyStdLibs.Arithmetic.Logarithm
  import opened DafnyStdLibs.Arithmetic.Power
  import opened DafnyStdLibs.Arithmetic.Mul

  /* log_b(m * n) = log_b(m) + log_b(n) if m and n are also powers of b */
  lemma LogProductRule(b: nat, x: nat, y: nat)
    requires b > 1
    ensures (
              LemmaPowPositive(b, x);
              LemmaPowPositive(b, y);
              LemmaMulIncreases(Pow(b, x), Pow(b, y));
              Log(b, Pow(b, x) * Pow(b, y)) == Log(b, Pow(b, x)) + Log(b, Pow(b, y))
            )
  {
    LemmaPowAdds(b, x, y);
    LemmaLogPow(b, x + y);
    LemmaLogPow(b, x);
    LemmaLogPow(b, y);
  }

  module DecimalLittleEndian refines DafnyStdLibs.Arithmetic.LittleEndianNat {
    function BASE(): nat {
      10
    }

    method {:test} TestFromNat() {
      expect FromNat(0) == [];
      expect FromNat(1) == [1];
      expect FromNat(3) == [3];
      expect FromNat(302) == [2, 0, 3];
    }

    method {:test} TestToNatRight() {
      expect ToNatRight([0]) == 0;
      expect ToNatRight([1]) == 1;
      expect ToNatRight([3]) == 3;
      expect ToNatRight([3,0,2]) == 203;
    }

    method {:test} TestSeqExtend() {
      expect SeqExtend([], 3) == [0, 0, 0];
      expect SeqExtend([1], 3) == [1, 0, 0];
      expect SeqExtend([3,0,2], 4) == [3,0,2,0];
    }

    method {:test} TestSeqExtendMultiple() {
      expect SeqExtendMultiple([], 3) == [0, 0, 0];
      print "length: ", |SeqExtendMultiple([1, 2, 3], 3)|;
      expect SeqExtendMultiple([1, 2], 3) == [1, 2, 0];
      expect SeqExtendMultiple([1, 2, 3], 3) == [1, 2, 3, 0, 0, 0];
      expect SeqExtendMultiple([3, 0, 2, 3], 3) == [3, 0, 2, 3, 0, 0];
    }

    method {:test} TestFromNatWithLen() {
      reveal Pow();
      expect FromNatWithLen(100, 4) == [0, 0, 1, 0];
    }

    method {:test} TestSeqZero() {
      expect SeqZero(3) == [0, 0, 0];
    }

    method {:test} TestSeqAdd() {
      expect SeqAdd([9,9,9],[9,9,9]) == ([8,9,9], 1);
      expect SeqAdd([9,9,9],[0,0,0]) == ([9,9,9], 0);
      expect SeqAdd([4,9,9],[5,0,0]) == ([9,9,9], 0);
    }

    method {:test} TestSeqSub() {
      expect SeqSub([9,9,9],[0,0,0]) == ([9,9,9], 0);
      expect SeqSub([9,9,9],[0,0,1]) == ([9,9,8], 0);
      expect SeqSub([0],[1]) == ([9], 1);
      expect SeqSub([0,0,0],[1,0,0]) == ([9,9,9], 1);
    }
  }
}