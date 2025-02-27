function Factorial(n: nat): nat
{
  if n == 0 then
    1
  else
    n * Factorial(n - 1)
}
// pure-end

method IterativeFactorial(n: nat) returns (result: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result == Factorial(n)
  // post-conditions-end
{
// impl-start
  result := 1;
  var i := 1;
  while i <= n
    // invariants-start

    invariant i <= n + 1
    invariant result == Factorial(i - 1)
    // invariants-end

  {
    result := result * i;
    i := i + 1;
  }
// impl-end
}
