function power(a: int, n: int): int
  requires 0 <= n
  decreases n
{
  if n == 0 then
    1
  else
    a * power(a, n - 1)
}
// pure-end

method A8Q1(y0: int, x: int) returns (z: int)
  // pre-conditions-start
  requires y0 >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures z == power(x, y0)
  // post-conditions-end
{
// impl-start
  var y := y0;
  z := 1;
  while y > 0
    // invariants-start

    invariant z == power(x, y0 - y) && y >= 0
    decreases y
    // invariants-end

  {
    z := z * x;
    y := y - 1;
  }
// impl-end
}
