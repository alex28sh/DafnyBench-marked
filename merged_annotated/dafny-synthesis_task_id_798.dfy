function sumTo(a: array<int>, n: int): int
  requires a != null
  requires 0 <= n && n <= a.Length
  reads a
  decreases n
{
  if n == 0 then
    0
  else
    sumTo(a, n - 1) + a[n - 1]
}
// pure-end

method ArraySum(a: array<int>) returns (result: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result == sumTo(a, a.Length)
  // post-conditions-end
{
// impl-start
  result := 0;
  for i := 0 to a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant result == sumTo(a, i)
    // invariants-end

  {
    result := result + a[i];
  }
// impl-end
}
