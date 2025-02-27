function f(n: int): int
{
  if n < 0 then
    0
  else
    3 * f(n - 5) + n
}
// pure-end

method problem5(n: nat) returns (x: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures x == f(n)
  // post-conditions-end
{
// impl-start
  var a := 1;
  var b := 0;
  var k := n;
  while k >= 0
    // invariants-start

    invariant f(n) == a * f(k) + b
    invariant -5 <= k <= n
    decreases k
    // invariants-end

  {
    // assert-start
    assert f(n) == a * f(k) + b;
    // assert-end

    // assert-start
    assert f(n) == a * (3 * f(k - 5) + k) + b;
    // assert-end

    // assert-start
    assert f(n) == 3 * a * f(k - 5) + a * k + b;
    // assert-end

    b := a * k + b;
    // assert-start
    assert f(n) == 3 * a * f(k - 5) + b;
    // assert-end

    a := 3 * a;
    // assert-start
    assert f(n) == a * f(k - 5) + b;
    // assert-end

    k := k - 5;
    // assert-start
    assert f(n) == a * f(k) + b;
    // assert-end

  }
  // assert-start
  assert k < 0;
  // assert-end

  // assert-start
  assert f(n) == a * f(k) + b;
  // assert-end

  // assert-start
  assert f(n) == a * 0 + b;
  // assert-end

  x := b;
  // assert-start
  assert x == f(n);
  // assert-end

// impl-end
}
