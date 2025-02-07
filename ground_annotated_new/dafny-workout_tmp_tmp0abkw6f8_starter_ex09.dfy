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
  var i: int := 1;
  if 0 <= n < 2 {
    return n;
  }
  b := 1;
  var c := 1;
  while i < n
    // invariants-start

    invariant 0 < i <= n
    invariant b == fib(i)
    invariant c == fib(i + 1)
    decreases n - i
    // invariants-end

  {
    b, c := c, b + c;
    i := i + 1;
  }
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var ret := ComputeFib(5);
  // assert-start
  assert ret == fib(5);
  // assert-end

// impl-end
}
