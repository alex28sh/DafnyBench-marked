method SumOfSquaresOfFirstNOddNumbers(n: int) returns (sum: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures sum == n * (2 * n - 1) * (2 * n + 1) / 3
  // post-conditions-end
{
// impl-start
  sum := 0;
  var i := 1;
  for k := 0 to n
    // invariants-start

    invariant 0 <= k <= n
    invariant sum == k * (2 * k - 1) * (2 * k + 1) / 3
    invariant i == 2 * k + 1
    // invariants-end

  {
    sum := sum + i * i;
    i := i + 2;
  }
// impl-end
}
