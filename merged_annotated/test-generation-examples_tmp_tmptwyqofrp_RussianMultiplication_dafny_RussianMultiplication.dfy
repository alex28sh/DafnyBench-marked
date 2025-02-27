// test-generation-examples_tmp_tmptwyqofrp_RussianMultiplication_dafny_RussianMultiplication.dfy


module RussianMultiplication {
  method mult(n0: int, m0: int) returns (res: int)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures res == n0 * m0
    // post-conditions-end
  {
  // impl-start
    var n, m: int;
    res := 0;
    if n0 >= 0 {
      n, m := n0, m0;
    } else {
      n, m := -n0, -m0;
    }
    while 0 < n
      // invariants-start

      invariant m * n + res == m0 * n0
      decreases n
      // invariants-end

    {
      res := res + m;
      n := n - 1;
    }
  // impl-end
  }
}
