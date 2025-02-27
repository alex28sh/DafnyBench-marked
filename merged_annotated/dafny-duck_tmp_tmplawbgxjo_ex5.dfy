function expo(x: int, n: nat): int
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
  ensures (expo(2, 3 * n) - expo(3, n)) % (2 + 3) == 0
  // post-conditions-end
{
// impl-start
  if n == 0 {
    assert (expo(2, 3 * 0) - expo(3, 0)) % 5 == 0;
  } else if n == 1 {
    assert (expo(2, 3 * 1) - expo(3, 1)) % 5 == 0;
  } else {
    Expon23(n - 1);
    assert (expo(2, 3 * (n - 1)) - expo(3, n - 1)) % 5 == 0;
    assert expo(2, 3 * n) == expo(2, 3 * (n - 1) + 2) * expo(2, 1);
    assert expo(2, 3 * n) == expo(2, 3 * (n - 1) + 3);
    assert expo(2, 3 * (n - 1) + 3) == expo(2, 3 * (n - 1) + 1) * expo(2, 2);
    assert expo(2, 3 * (n - 1) + 3) == expo(2, 3 * (n - 1)) * expo(2, 3);
    assert expo(3, n - 1 + 1) == expo(3, n - 1) * expo(3, 1);
    assert expo(3, n) == expo(3, n - 1) * expo(3, 1);
    assert expo(3, n) == expo(3, n - 1 + 1);
    assert expo(2, 3 * (n - 1)) * expo(2, 3) == expo(2, 3 * (n - 1)) * 8;
    assert expo(3, n - 1) * expo(3, 1) == expo(3, n - 1) * 3;
    assert expo(2, 3 * n) - expo(3, n) == expo(2, 3 * (n - 1) + 3) - expo(3, n - 1 + 1);
    assert (expo(2, 3 * n) - expo(3, n)) % 5 == (expo(2, 3 * (n - 1) + 3) - expo(3, n - 1 + 1)) % 5;
    assert (expo(2, 3 * n) - expo(3, n)) % 5 == (expo(2, 3 * (n - 1)) * expo(2, 3) - expo(3, n - 1) * expo(3, 1)) % 5;
    assert (expo(2, 3 * n) - expo(3, n)) % 5 == (expo(2, 3 * (n - 1)) * 8 - expo(3, n - 1) * 3) % 5;
    assert (expo(2, 3 * n) - expo(3, n)) % 5 == (expo(2, 3 * (n - 1)) * 8 - expo(3, n - 1) * 8 + expo(3, n - 1) * 8 - expo(3, n - 1) * 3) % 5;
    assert (expo(2, 3 * n) - expo(3, n)) % 5 == (8 * (expo(2, 3 * (n - 1)) - expo(3, n - 1)) + expo(3, n - 1) * (8 - 3)) % 5;
    assert (expo(2, 3 * n) - expo(3, n)) % 5 == (8 * (expo(2, 3 * (n - 1)) - expo(3, n - 1)) + expo(3, n - 1) * 5) % 5;
    assert (expo(2, 3 * n) - expo(3, n)) % 5 == (8 * (expo(2, 3 * (n - 1)) - expo(3, n - 1)) % 5 + expo(3, n - 1) * 5 % 5) % 5;
    assert (expo(2, 3 * n) - expo(3, n)) % 5 == 0;
  }
// impl-end
}
