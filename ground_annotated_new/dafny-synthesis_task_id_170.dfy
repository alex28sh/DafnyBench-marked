function sumTo(a: array<int>, start: int, end: int): int
  requires a != null
  requires 0 <= start && start <= end && end <= a.Length
  reads a
  decreases end
{
  if start == end then
    0
  else
    sumTo(a, start, end - 1) + a[end - 1]
}
// pure-end

method SumInRange(a: array<int>, start: int, end: int)
    returns (sum: int)
  // pre-conditions-start
  requires a != null
  requires 0 <= start && start <= end && end <= a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures sum == sumTo(a, start, end)
  // post-conditions-end
{
// impl-start
  sum := 0;
  for i := start to end
    // invariants-start

    invariant start <= i <= end
    invariant sum == sumTo(a, start, i)
    // invariants-end

  {
    sum := sum + a[i];
  }
// impl-end
}
