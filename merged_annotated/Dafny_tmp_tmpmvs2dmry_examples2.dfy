method add_by_inc(x: nat, y: nat) returns (z: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures z == x + y
  // post-conditions-end
{
// impl-start
  z := x;
  var i := 0;
  while i < y
    // invariants-start

    invariant 0 <= i <= y
    invariant z == x + i
    decreases y - i
    // invariants-end

  {
    z := z + 1;
    i := i + 1;
  }
  // assert-start
  assert z == x + y;
  // assert-end

  // assert-start
  assert i == y;
  // assert-end

// impl-end
}

method Product(m: nat, n: nat) returns (res: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures res == m * n
  // post-conditions-end
{
// impl-start
  var m1: nat := m;
  res := 0;
  while m1 != 0
    // invariants-start

    invariant 0 <= m1 <= m
    invariant res == (m - m1) * n
    decreases m1
    // invariants-end

  {
    var n1: nat := n;
    while n1 != 0
      // invariants-start

      invariant 0 <= n1 <= n
      invariant res == (m - m1) * n + (n - n1)
      decreases n1
      // invariants-end

    {
      res := res + 1;
      n1 := n1 - 1;
    }
    m1 := m1 - 1;
  }
// impl-end
}

method gcdCalc(m: nat, n: nat) returns (res: nat)
  // pre-conditions-start
  requires m > 0 && n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures res == gcd(m, n)
  // post-conditions-end
{
// impl-start
  var m1: nat := m;
  var n1: nat := n;
  while m1 != n1
    // invariants-start

    invariant 0 < m1 <= m
    invariant 0 < n1 <= n
    invariant gcd(m, n) == gcd(m1, n1)
    decreases m1 + n1
    // invariants-end

  {
    if m1 > n1 {
      m1 := m1 - n1;
    } else {
      n1 := n1 - m1;
    }
  }
  return n1;
// impl-end
}

function gcd(m: nat, n: nat): nat
  requires m > 0 && n > 0
  decreases m + n
{
  if m == n then
    n
  else if m > n then
    gcd(m - n, n)
  else
    gcd(m, n - m)
}
// pure-end

method exp_by_sqr(x0: real, n0: nat) returns (r: real)
  // pre-conditions-start
  requires x0 >= 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures r == exp(x0, n0)
  // post-conditions-end
{
// impl-start
  if n0 == 0 {
    return 1.0;
  }
  if x0 == 0.0 {
    return 0.0;
  }
  var x, n, y := x0, n0, 1.0;
  while n > 1
    // invariants-start

    invariant 1 <= n <= n0
    invariant exp(x0, n0) == exp(x, n) * y
    decreases n
    // invariants-end

  {
    if n % 2 == 0 {
      // assert-start
      assume exp(x, n) == exp(x * x, n / 2);
      // assert-end

      x := x * x;
      n := n / 2;
    } else {
      // assert-start
      assume exp(x, n) == exp(x * x, (n - 1) / 2) * x;
      // assert-end

      y := x * y;
      x := x * x;
      n := (n - 1) / 2;
    }
  }
  return x * y;
// impl-end
}

function exp(x: real, n: nat): real
  decreases n
{
  if n == 0 then
    1.0
  else if x == 0.0 then
    0.0
  else if n == 0 && x == 0.0 then
    1.0
  else
    x * exp(x, n - 1)
}
// pure-end
