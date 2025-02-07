function fact(n: nat): nat
  ensures fact(n) >= 1
{
  if n == 0 then
    1
  else
    n * fact(n - 1)
}
// pure-end

method factorial(n: nat) returns (res: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures res == fact(n)
  // post-conditions-end
{
// impl-start
  var i := 1;
  res := 1;
  while i < n + 1
    // invariants-start

    invariant 0 < i <= n + 1
    invariant res == fact(i - 1)
    // invariants-end

  {
    res := i * res;
    i := i + 1;
  }
// impl-end
}
