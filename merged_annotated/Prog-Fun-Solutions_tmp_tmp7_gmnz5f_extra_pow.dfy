function pow(a: int, e: nat): int
{
  if e == 0 then
    1
  else
    a * pow(a, e - 1)
}
// pure-end

method Pow(a: nat, n: nat) returns (y: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures y == pow(a, n)
  // post-conditions-end
{
// impl-start
  var x: nat := 1;
  var k: nat := 0;
  while k < n
    // invariants-start

    invariant x == pow(a, k)
    invariant 0 <= k <= n
    decreases n - k
    // invariants-end

  {
    // assert-start
    assert x == pow(a, k);
    // assert-end

    x := a * x;
    // assert-start
    assert x == a * pow(a, k);
    // assert-end

    // assert-start
    assert x == pow(a, k + 1);
    // assert-end

    k := k + 1;
    // assert-start
    assert x == pow(a, k);
    // assert-end

  }
  // assert-start
  assert k == n;
  // assert-end

  y := x;
  // assert-start
  assert y == pow(a, n);
  // assert-end

// impl-end
}
