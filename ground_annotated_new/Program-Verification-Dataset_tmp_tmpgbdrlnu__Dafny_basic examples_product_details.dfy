method CalcProduct(m: nat, n: nat) returns (res: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures res == m * n
  // post-conditions-end
{
// impl-start
  var m1: nat := m;
  res := 0;
  // assert-start
  assert res == (m - m1) * n;
  // assert-end

  m1, res := *, *;
  // assert-start
  assume res == (m - m1) * n;
  // assert-end

  if m1 != 0 {
    var n1: nat := n;
    // assert-start
    assert res == (m - m1) * n + (n - n1);
    // assert-end

    res, n1 := *, *;
    // assert-start
    assume res == (m - m1) * n + (n - n1);
    // assert-end

    if n1 != 0 {
      ghost var old_n1 := n1;
      res := res + 1;
      n1 := n1 - 1;
      // assert-start
      assert res == (m - m1) * n + (n - n1);
      // assert-end

      // assert-start
      assert n1 < old_n1;
      // assert-end

      // assert-start
      assert n1 >= 0;
      // assert-end

      // assert-start
      assume false;
      // assert-end

    }
    m1 := m1 - 1;
    // assert-start
    assert res == (m - m1) * n;
    // assert-end

    // assert-start
    assume false;
    // assert-end

  }
// impl-end
}
