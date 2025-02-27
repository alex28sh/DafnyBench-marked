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
  var x, y := m, n;
  d := 1;
  while x != y
    // invariants-start

    invariant x > 0 && y > 0
    invariant gcd(x, y) == gcd(m, n)
    decreases x + y
    // invariants-end

  {
    if x > y {
      x := x - y;
    } else {
      y := y - x;
    }
  }
  d := x;
// impl-end
}

function gcd'(x: int, y: int): int
  requires x > 0 && y > 0
  decreases x + y, y
{
  if x == y then
    x
  else if x > y then
    gcd'(x - y, y)
  else
    gcd'(y, x)
}
// pure-end
