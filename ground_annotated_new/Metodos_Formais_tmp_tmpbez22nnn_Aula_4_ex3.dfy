function Fib(n: nat): nat
{
  if n < 2 then
    n
  else
    Fib(n - 2) + Fib(n - 1)
}
// pure-end

method ComputeFib(n: nat) returns (x: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures x == Fib(n)
  // post-conditions-end
{
// impl-start
  var i := 0;
  x := 0;
  var y := 1;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant x == Fib(i)
    invariant y == Fib(i + 1)
    decreases n - i
    // invariants-end

  {
    x, y := y, x + y;
    i := i + 1;
  }
// impl-end
}

method Teste()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var n := 3;
  var f := ComputeFib(n);
  // assert-start
  assert f == 2;
  // assert-end

// impl-end
}
