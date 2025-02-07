method SumAndAverage(n: int) returns (sum: int, average: real)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures sum == n * (n + 1) / 2
  ensures average == sum as real / n as real
  // post-conditions-end
{
// impl-start
  sum := 0;
  for i := 1 to n + 1
    // invariants-start

    invariant 0 <= i <= n + 1
    invariant sum == (i - 1) * i / 2
    // invariants-end

  {
    sum := sum + i;
  }
  average := sum as real / n as real;
// impl-end
}
