method sumOdds(n: nat) returns (sum: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures sum == n * n
  // post-conditions-end
{
// impl-start
  sum := 1;
  var i := 0;
  while i < n - 1
    // invariants-start

    invariant 0 <= i < n
    invariant sum == (i + 1) * (i + 1)
    // invariants-end

  {
    i := i + 1;
    sum := sum + 2 * i + 1;
  }
  // assert-start
  assert sum == n * n;
  // assert-end

// impl-end
}

method intDiv(n: int, d: int)
    returns (q: int, r: int)
  // pre-conditions-start
  requires n >= d && n >= 0 && d > 0
  // pre-conditions-end
  // post-conditions-start
  ensures d * q + r == n && 0 <= q <= n / 2 && 0 <= r < d
  // post-conditions-end

method intDivImpl(n: int, d: int)
    returns (q: int, r: int)
  // pre-conditions-start
  requires n >= d && n >= 0 && d > 0
  // pre-conditions-end
  // post-conditions-start
  ensures d * q + r == n && 0 <= q <= n / 2 && 0 <= r < d
  // post-conditions-end
{
// impl-start
  q := 0;
  r := n;
  while r >= d
    // invariants-start

    invariant r == n - q * d
    invariant d <= r
    // invariants-end

  r := r - 1;
  {
    r := r - d;
    q := q + 1;
  }
  // assert-start
  assert n == d * q + r;
  // assert-end

// impl-end
}
