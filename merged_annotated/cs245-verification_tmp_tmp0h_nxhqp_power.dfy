// cs245-verification_tmp_tmp0h_nxhqp_power.dfy

function power(a: int, n: int): int
  requires 0 <= a && 0 <= n
  decreases n
{
  if n == 0 then
    1
  else
    a * power(a, n - 1)
}
// pure-end

method compute_power(a: int, n: int) returns (s: int)
  // pre-conditions-start
  requires n >= 0 && a >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures s == power(a, n)
  // post-conditions-end
{
// impl-start
  // assert-start
  assert 1 == power(a, 0) && 0 <= n;
  // assert-end

  s := 1;
  // assert-start
  assert s == power(a, 0) && 0 <= n;
  // assert-end

  var i := 0;
  // assert-start
  assert s == power(a, i) && i <= n;
  // assert-end

  while i < n
    // invariants-start

    invariant s == power(a, i) && i <= n
    decreases n - i
    // invariants-end

  {
    // assert-start
    assert s == power(a, i) && i <= n && i < n;
    // assert-end

    // assert-start
    assert s * a == power(a, i + 1) && i + 1 <= n;
    // assert-end

    s := s * a;
    // assert-start
    assert s == power(a, i + 1) && i + 1 <= n;
    // assert-end

    i := i + 1;
    // assert-start
    assert s == power(a, i) && i <= n;
    // assert-end

  }
  // assert-start
  assert s == power(a, i) && i <= n && !(i < n);
  // assert-end

// impl-end
}
