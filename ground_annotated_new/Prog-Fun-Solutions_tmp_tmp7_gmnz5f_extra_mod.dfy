function f(n: nat): nat
{
  if n == 0 then
    1
  else if n % 2 == 0 then
    1 + 2 * f(n / 2)
  else
    2 * f(n / 2)
}
// pure-end

method mod(n: nat) returns (a: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a == f(n)
  // post-conditions-end
{
// impl-start
  var x: nat := 0;
  var y: nat := 1;
  var k: nat := n;
  while k > 0
    // invariants-start

    invariant f(n) == x + y * f(k)
    invariant 0 <= k <= n
    decreases k
    // invariants-end

  {
    // assert-start
    assert f(n) == x + y * f(k);
    // assert-end

    if k % 2 == 0 {
      // assert-start
      assert f(n) == x + y * f(k);
      // assert-end

      // assert-start
      assert f(n) == x + y * (1 + 2 * f(k / 2));
      // assert-end

      // assert-start
      assert f(n) == x + y + 2 * y * f(k / 2);
      // assert-end

      x := x + y;
      // assert-start
      assert f(n) == x + 2 * y * f(k / 2);
      // assert-end

    } else {
      // assert-start
      assert f(n) == x + y * (2 * f(k / 2));
      // assert-end

      // assert-start
      assert f(n) == x + 2 * y * f(k / 2);
      // assert-end

    }
    y := 2 * y;
    // assert-start
    assert f(n) == x + y * f(k / 2);
    // assert-end

    k := k / 2;
    // assert-start
    assert f(n) == x + y * f(k);
    // assert-end

  }
  // assert-start
  assert k == 0;
  // assert-end

  // assert-start
  assert f(n) == x + y * f(0);
  // assert-end

  // assert-start
  assert f(n) == x + y;
  // assert-end

  a := x + y;
// impl-end
}
