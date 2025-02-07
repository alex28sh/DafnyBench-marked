method SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15
  // post-conditions-end
{
// impl-start
  sum := 0;
  var i := 1;
  for k := 0 to n
    // invariants-start

    invariant 0 <= k <= n
    invariant i == 2 * k + 1
    invariant sum == k * (2 * k + 1) * (24 * k * k * k - 12 * k * k - 14 * k + 7) / 15
    // invariants-end

  {
    sum := sum + i * i * i * i;
    i := i + 2;
  }
// impl-end
}
