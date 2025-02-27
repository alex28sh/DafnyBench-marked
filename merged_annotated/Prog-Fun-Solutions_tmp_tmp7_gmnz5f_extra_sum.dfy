function sum(n: nat): int
{
  if n == 0 then
    0
  else
    n + sum(n - 1)
}
// pure-end

method Sum(n: nat) returns (s: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures s == sum(n)
  // post-conditions-end
{
// impl-start
  var x: nat := 0;
  var y: nat := 1;
  var k: nat := n;
  while k > 0
    // invariants-start

    invariant sum(n) == x + y * sum(k)
    invariant 0 <= k <= n
    decreases k
    // invariants-end

  {
    // assert-start
    assert sum(n) == x + y * sum(k);
    // assert-end

    // assert-start
    assert sum(n) == x + y * (k + sum(k - 1));
    // assert-end

    // assert-start
    assert sum(n) == x + y * k + y * sum(k - 1);
    // assert-end

    x := x + y * k;
    // assert-start
    assert sum(n) == x + y * sum(k - 1);
    // assert-end

    // assert-start
    assert sum(n) == x + y * sum(k - 1);
    // assert-end

    k := k - 1;
    // assert-start
    assert sum(n) == x + y * sum(k);
    // assert-end

  }
  // assert-start
  assert k == 0;
  // assert-end

  // assert-start
  assert sum(n) == x + y * sum(0);
  // assert-end

  // assert-start
  assert sum(n) == x + y * 0;
  // assert-end

  s := x;
  // assert-start
  assert sum(n) == s;
  // assert-end

// impl-end
}
