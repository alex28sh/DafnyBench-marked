method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures diff == n * n * (n + 1) * (n + 1) / 4 - n * (n + 1) / 2
  // post-conditions-end
{
// impl-start
  var sumCubes := 0;
  var sumNumbers := 0;
  for i := 1 to n + 1
    // invariants-start

    invariant 0 <= i <= n + 1
    invariant sumCubes == (i - 1) * (i - 1) * i * i / 4
    invariant sumNumbers == (i - 1) * i / 2
    // invariants-end

  {
    sumCubes := sumCubes + i * i * i;
    sumNumbers := sumNumbers + i;
  }
  diff := sumCubes - sumNumbers;
// impl-end
}
