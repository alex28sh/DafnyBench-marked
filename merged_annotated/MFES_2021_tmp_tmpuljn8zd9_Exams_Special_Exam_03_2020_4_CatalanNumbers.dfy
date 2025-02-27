function C(n: nat): nat
  decreases n
{
  if n == 0 then
    1
  else
    (4 * n - 2) * C(n - 1) / (n + 1)
}
// pure-end

method calcC(n: nat) returns (res: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures res == C(n)
  // post-conditions-end
{
// impl-start
  var i := 0;
  res := 1;
  // assert-start
  assert res == C(i) && 0 <= i <= n;
  // assert-end

  while i < n
    // invariants-start

    invariant res == C(i) && 0 <= i <= n
    decreases n - i
    // invariants-end

  {
    ghost var v0 := n - i;
    // assert-start
    assert res == C(i) && 0 <= i <= n && i < n && n - i == v0;
    // assert-end

    i := i + 1;
    res := (4 * i - 2) * res / (i + 1);
    // assert-start
    assert res == C(i) && 0 <= i <= n && 0 <= n - i < v0;
    // assert-end

  }
  // assert-start
  assert res == C(i) && 0 <= i <= n && i >= n;
  // assert-end

// impl-end
}
