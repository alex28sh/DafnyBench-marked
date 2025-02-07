function sumNegativesTo(a: array<int>, n: int): int
  requires a != null
  requires 0 <= n && n <= a.Length
  reads a
  decreases n
{
  if n == 0 then
    0
  else if a[n - 1] < 0 then
    sumNegativesTo(a, n - 1) + a[n - 1]
  else
    sumNegativesTo(a, n - 1)
}
// pure-end

method SumOfNegatives(a: array<int>) returns (result: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result == sumNegativesTo(a, a.Length)
  // post-conditions-end
{
// impl-start
  result := 0;
  for i := 0 to a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant result == sumNegativesTo(a, i)
    // invariants-end

  {
    if a[i] < 0 {
      result := result + a[i];
    }
  }
// impl-end
}
