function fib(n: nat): nat
  decreases n
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    fib(n - 1) + fib(n - 2)
}
// pure-end

method ComputeFib(n: nat) returns (f: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures f == fib(n)
  // post-conditions-end
{
// impl-start
  if n == 0 {
    f := 0;
  } else {
    var i := 1;
    var f_2 := 0;
    var f_1 := 0;
    f := 1;
    while i < n
      // invariants-start

      invariant i <= n
      invariant f_1 == fib(i - 1)
      invariant f == fib(i)
      decreases n - i
      // invariants-end

    {
      f_2 := f_1;
      f_1 := f;
      f := f_1 + f_2;
      i := i + 1;
    }
  }
// impl-end
}
