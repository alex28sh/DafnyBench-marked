function expo(x: int, n: nat): int
  requires n >= 0
{
  if n == 0 then
    1
  else
    x * expo(x, n - 1)
}
// pure-end

lemma {:induction false} Expon23(n: nat)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures (expo(2, 3 * n) - expo(3, n)) % 5 == 0
  // post-conditions-end
{
// impl-start
  if n == 0 {
    assert (expo(2, 3 * 0) - expo(3, 0)) % 5 == 0;
  } else if n == 1 {
    assert (expo(2, 3 * 1) - expo(3, 1)) % 5 == 0;
  } else {
    var i: nat := n;
    var j: nat := n;
    Expon23(n - 1);
    assert (expo(2, 3 * (i - 1)) - expo(3, i - 1)) % 5 == 0;
    assert (expo(2, 3 * i - 3) - expo(3, n - 1)) % 5 == 0;
    assert expo(2, i - 0) == expo(2, i);
    assert expo(2, i - 1) == expo(2, i) / expo(2, 1);
    assert expo(2, 1 * i - 0) == expo(2, 1 * i);
    assert expo(2, 2 * i - 1) == expo(2, 2 * i) / expo(2, 1);
    assert expo(2, 3 * 1 - 3) == expo(2, 3 * 1) / expo(2, 3);
    assert expo(2, 3 * i - 0) == expo(2, 3 * i);
    assert expo(2, 3 * i - 1) == expo(2, 3 * i) / expo(2, 1);
    assert expo(2, 3 * i - 2) == expo(2, 3 * i) / expo(2, 2);
    assert expo(2, 3 * i - 3) == expo(2, 3 * i) / expo(2, 3);
    assert expo(3, i - 1) == expo(3, i) / expo(3, 1);
    assert expo(2, 3 * i - 3) - expo(3, i - 1) == expo(2, 3 * i) / expo(2, 3) - expo(3, i) / expo(3, 1);
    assert expo(2, 3) % 5 == expo(3, 1);
    assert expo(2, 3 * i) * 6 % 5 == expo(2, 3 * i) % 5;
    assert expo(2, 3 * i) * expo(2, 3) % 5 == expo(2, 3 * i) * expo(3, 1) % 5;
    assert (expo(2, 3 * i) * expo(2, 3) - expo(3, i) * expo(3, 1)) % 5 == (expo(2, 3 * i) * expo(3, 1) - expo(3, i) * expo(3, 1)) % 5;
    assert (expo(2, 3 * i) * expo(3, 1) - expo(3, i) * expo(3, 1)) % 5 == expo(3, 1) * (expo(2, 3 * i) - expo(3, i)) % 5;
    assert (expo(2, 3 * i) - expo(3, i)) % 5 == 0;
  }
// impl-end
}

method check()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert expo(2, 3) == 8;
  // assert-end

  // assert-start
  assert expo(-2, 3) == -8;
  // assert-end

  // assert-start
  assert expo(3, 0) == 1;
  // assert-end

  // assert-start
  assert expo(0, 0) == 1;
  // assert-end

  // assert-start
  assert expo(10, 2) == 100;
  // assert-end

// impl-end
}
