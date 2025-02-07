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

method fibonacci1(n: nat) returns (f: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures f == fib(n)
  // post-conditions-end
{
// impl-start
  var i := 0;
  f := 0;
  var fsig := 1;
  while i < n
    // invariants-start

    invariant f == fib(i) && fsig == fib(i + 1)
    invariant i <= n
    decreases n - i
    // invariants-end

  {
    f, fsig := fsig, f + fsig;
    i := i + 1;
  }
// impl-end
}

method fibonacci2(n: nat) returns (f: nat)
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
    var fant := 0;
    f := 1;
    while i < n
      // invariants-start

      invariant fant == fib(i - 1) && f == fib(i)
      invariant i <= n
      decreases n - i
      // invariants-end

    {
      fant, f := f, fant + f;
      i := i + 1;
    }
  }
// impl-end
}

method fibonacci3(n: nat) returns (f: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures f == fib(n)
  // post-conditions-end
{
// impl-start
  {
    var i: int := 0;
    var a := 1;
    f := 0;
    while i < n
      // invariants-start

      invariant 0 <= i <= n
      invariant if i == 0 then a == fib(i + 1) && f == fib(i) else a == fib(i - 1) && f == fib(i)
      decreases n - i
      // invariants-end

    {
      a, f := f, a + f;
      i := i + 1;
    }
  }
// impl-end
}
