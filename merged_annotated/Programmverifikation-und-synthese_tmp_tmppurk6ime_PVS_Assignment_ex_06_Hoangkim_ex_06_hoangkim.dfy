function gcd(x: int, y: int): int
  requires x > 0 && y > 0
{
  if x == y then
    x
  else if x > y then
    gcd(x - y, y)
  else
    gcd(x, y - x)
}
// pure-end

method gcdI(m: int, n: int) returns (d: int)
  // pre-conditions-start
  requires m > 0 && n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures d == gcd(m, n)
  // post-conditions-end
{
// impl-start
  var x: int;
  d := m;
  x := n;
  while d != x
    // invariants-start

    invariant x > 0
    invariant d > 0
    invariant gcd(d, x) == gcd(m, n)
    decreases x + d
    // invariants-end

  {
    if d > x {
      d := d - x;
    } else {
      x := x - d;
    }
  }
// impl-end
}

function gcd'(x: int, y: int): int
  requires x > 0 && y > 0
  decreases if x > y then x else y
{
  if x == y then
    x
  else if x > y then
    gcd'(x - y, y)
  else
    gcd(y, x)
}
// pure-end
