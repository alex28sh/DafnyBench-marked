function Fibonacci(n: nat): nat
{
  match n {
    case 0 =>
      0
    case 1 =>
      1
    case _ /* _v0 */ =>
      Fibonacci(n - 1) + Fibonacci(n - 2)
  }
}
// pure-end

method FibonacciIterative(n: nat) returns (f: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures f == Fibonacci(n)
  // post-conditions-end
{
// impl-start
  if n < 2 {
    return n;
  }
  var prev := 1;
  f := 1;
  var i := 2;
  while i < n
    // invariants-start

    invariant i <= n
    invariant prev == Fibonacci(i - 1)
    invariant f == Fibonacci(i)
    // invariants-end

  {
    prev, f := f, f + prev;
    i := i + 1;
  }
// impl-end
}
