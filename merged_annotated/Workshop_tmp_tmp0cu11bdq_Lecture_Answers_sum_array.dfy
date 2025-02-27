function sumTo(a: array<int>, n: int): int
  requires a != null
  requires 0 <= n && n <= a.Length
  reads a
{
  if n == 0 then
    0
  else
    sumTo(a, n - 1) + a[n - 1]
}
// pure-end

method sum_array(a: array<int>) returns (sum: int)
  // pre-conditions-start
  requires a != null
  // pre-conditions-end
  // post-conditions-start
  ensures sum == sumTo(a, a.Length)
  // post-conditions-end
{
// impl-start
  var i := 0;
  sum := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant sum == sumTo(a, i)
    // invariants-end

  {
    sum := sum + a[i];
    i := i + 1;
  }
// impl-end
}
