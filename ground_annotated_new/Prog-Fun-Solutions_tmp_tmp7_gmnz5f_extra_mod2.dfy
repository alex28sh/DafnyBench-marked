function f2(n: nat): nat
{
  if n == 0 then
    0
  else
    5 * f2(n / 3) + n % 4
}
// pure-end

method mod2(n: nat) returns (a: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a == f2(n)
  // post-conditions-end
{
// impl-start
  var x: nat := 1;
  var y: nat := 0;
  var k: nat := n;
  while k > 0
    // invariants-start

    invariant f2(n) == x * f2(k) + y
    invariant 0 <= k <= n
    decreases k
    // invariants-end

  {
    // assert-start
    assert f2(n) == x * f2(k) + y;
    // assert-end

    // assert-start
    assert f2(n) == x * (5 * f2(k / 3) + k % 4) + y;
    // assert-end

    // assert-start
    assert f2(n) == 5 * x * f2(k / 3) + x * (k % 4) + y;
    // assert-end

    y := x * (k % 4) + y;
    // assert-start
    assert f2(n) == 5 * x * f2(k / 3) + y;
    // assert-end

    x := 5 * x;
    // assert-start
    assert f2(n) == x * f2(k / 3) + y;
    // assert-end

    k := k / 3;
    // assert-start
    assert f2(n) == x * f2(k) + y;
    // assert-end

  }
  // assert-start
  assert k == 0;
  // assert-end

  // assert-start
  assert f2(n) == x * f2(0) + y;
  // assert-end

  // assert-start
  assert f2(n) == x * 0 + y;
  // assert-end

  // assert-start
  assert f2(n) == y;
  // assert-end

  a := y;
// impl-end
}
