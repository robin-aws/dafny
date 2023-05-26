method Main() returns () {
    var v_array: array<int> := new int[] [1, 2];

    var v_int_s: int := |{v_array}|;
    assert(v_int_s == 1);
    print v_int_s, "\n";

    var v_int_m: int := |multiset{v_array}|;
    assert(v_int_m == 1);
    print v_int_m, "\n";
}
