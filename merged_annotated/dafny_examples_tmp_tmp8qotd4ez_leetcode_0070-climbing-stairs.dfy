function Stairs(n: nat): nat
{
  if n <= 1 then
    1
  else
    Stairs(n - 2) + Stairs(n - 1)
}
// pure-end

method ClimbStairs(n: nat) returns (r: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == Stairs(n)
  // post-conditions-end
{
// impl-start
  var a, b := 1, 1;
  var i := 1;
  while i < n
    // invariants-start

    invariant i <= n || i == 1
    invariant a == Stairs(i - 1)
    invariant b == Stairs(i)
    // invariants-end

  {
    a, b := b, a + b;
    i := i + 1;
  }
  return b;
// impl-end
}
