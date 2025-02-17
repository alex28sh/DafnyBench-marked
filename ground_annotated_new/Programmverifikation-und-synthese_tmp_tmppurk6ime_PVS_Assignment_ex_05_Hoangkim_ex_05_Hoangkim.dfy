function fib(n: nat): nat
{
  if n < 2 then
    n
  else
    fib(n - 2) + fib(n - 1)
}
// pure-end

method fibIter(n: nat) returns (a: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures a == fib(n)
  // post-conditions-end
{
// impl-start
  a := 0;
  var b, x := 1, 0;
  while x < n
    // invariants-start

    invariant 0 <= x <= n
    invariant a == fib(x)
    invariant b == fib(x + 1)
    // invariants-end

  {
    a, b := b, a + b;
    x := x + 1;
  }
  // assert-start
  assert a == fib(n);
  // assert-end

// impl-end
}

function fact(n: nat): nat
{
  if n == 0 then
    1
  else
    n * fact(n - 1)
}
// pure-end

method factIter(n: nat) returns (a: nat)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures a == fact(n)
  // post-conditions-end
{
// impl-start
  a := 1;
  var i := 1;
  while i <= n
    // invariants-start

    invariant 1 <= i <= n + 1
    invariant a == fact(i - 1)
    // invariants-end

  {
    a := a * i;
    i := i + 1;
  }
  // assert-start
  assert a == fact(n);
  // assert-end

// impl-end
}

function gcd(m: nat, n: nat): nat
  requires m > 0 && n > 0
{
  if m == n then
    m
  else if m > n then
    gcd(m - n, n)
  else
    gcd(m, n - m)
}
// pure-end

method gcdI(m: int, n: int) returns (g: int)
  // pre-conditions-start
  requires m > 0 && n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures g == gcd(m, n)
  // post-conditions-end
{
// impl-start
  var x: int;
  g := m;
  x := n;
  while g != x
    // invariants-start

    invariant x > 0
    invariant g > 0
    invariant gcd(g, x) == gcd(m, n)
    decreases x + g
    // invariants-end

  {
    if g > x {
      g := g - x;
    } else {
      x := x - g;
    }
  }
// impl-end
}
