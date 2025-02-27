function f(n: int): int
{
  if n <= 0 then
    1
  else
    n + f(n - 1) * f(n - 2)
}
// pure-end

function fSum(n: nat): int
{
  if n <= 0 then
    0
  else
    f(n - 1) + fSum(n - 1)
}
// pure-end

method problem6(n: nat) returns (a: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a == fSum(n)
  // post-conditions-end
{
// impl-start
  a := 0;
  var k := 0;
  var x := 1;
  var y := 2;
  while k < n
    // invariants-start

    invariant 0 <= k <= n && x == f(k) && y == f(k + 1) && a == fSum(k)
    decreases n - k
    // invariants-end

  {
    // assert-start
    assert x == f(k) && y == f(k + 1) && a == fSum(k);
    // assert-end

    k := k + 1;
    // assert-start
    assert x == f(k - 1) && y == f(k) && a == fSum(k - 1);
    // assert-end

    // assert-start
    assert x == f(k - 1) && y == f(k) && a == fSum(k) - f(k - 1);
    // assert-end

    a := a + x;
    // assert-start
    assert x == f(k - 1) && y == f(k) && a == fSum(k) - f(k - 1) + f(k - 1);
    // assert-end

    // assert-start
    assert x == f(k - 1) && y == f(k) && a == fSum(k);
    // assert-end

    x, y := y, k + 1 + x * y;
    // assert-start
    assert x == f(k) && y == k + 1 + f(k - 1) * f(k) && a == fSum(k);
    // assert-end

    // assert-start
    assert x == f(k) && y == k + 1 + f(k + 1 - 2) * f(k + 1 - 1) && a == fSum(k);
    // assert-end

    // assert-start
    assert x == f(k) && y == f(k + 1) && a == fSum(k);
    // assert-end

  }
  // assert-start
  assert a == fSum(k);
  // assert-end

// impl-end
}
