function fib(n: nat): nat
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    fib(n - 1) + fib(n - 2)
}
// pure-end

method ComputeFib(n: nat) returns (b: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures b == fib(n)
  // post-conditions-end
{
// impl-start
  var i: int := 0;
  b := 0;
  var c := 1;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant b == fib(i)
    invariant c == fib(i + 1)
    // invariants-end

  {
    b, c := c, c + b;
    i := i + 1;
  }
// impl-end
}
