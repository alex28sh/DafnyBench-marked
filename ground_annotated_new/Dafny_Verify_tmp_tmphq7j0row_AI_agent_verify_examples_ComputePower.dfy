function Power(n: nat): nat
{
  if n == 0 then
    1
  else
    2 * Power(n - 1)
}
// pure-end

method ComputePower(N: int) returns (y: nat)
  // pre-conditions-start
  requires N >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures y == Power(N)
  // post-conditions-end
{
// impl-start
  y := 1;
  var x := 0;
  while x != N
    // invariants-start

    invariant 0 <= x <= N
    invariant y == Power(x)
    decreases N - x
    // invariants-end

  {
    x, y := x + 1, y + y;
  }
// impl-end
}
