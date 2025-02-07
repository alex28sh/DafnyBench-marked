function Factorial(n: nat): nat
{
  if n == 0 then
    1
  else
    n * Factorial(n - 1)
}
// pure-end

method ComputeFactorial(n: int) returns (u: int)
  // pre-conditions-start
  requires 1 <= n
  // pre-conditions-end
  // post-conditions-start
  ensures u == Factorial(n)
  // post-conditions-end
{
// impl-start
  var r := 1;
  u := 1;
  while r < n
    // invariants-start

    invariant r <= n
    invariant u == Factorial(r)
    // invariants-end

  {
    var v, s := u, 1;
    while s < r + 1
      // invariants-start

      invariant s <= r + 1
      invariant v == Factorial(r) && u == s * Factorial(r)
      // invariants-end

    {
      u := u + v;
      s := s + 1;
    }
    r := r + 1;
  }
// impl-end
}
