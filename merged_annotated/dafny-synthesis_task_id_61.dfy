function IsDigit(c: char): bool
{
  48 <= c as int <= 57
}
// pure-end

method CountSubstringsWithSumOfDigitsEqualToLength(s: string) returns (count: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures count >= 0
  // post-conditions-end
{
// impl-start
  count := 0;
  for i := 0 to |s|
    // invariants-start

    invariant 0 <= i <= |s|
    // invariants-end

  {
    var sum := 0;
    for j := i to |s|
      // invariants-start

      invariant i <= j <= |s|
      invariant sum >= 0
      invariant sum <= j - i
      // invariants-end

    {
      if j == |s| || !IsDigit(s[j]) {
        if sum == j - i {
          count := count + 1;
        }
        break;
      }
      sum := sum + (s[j] as int - 48);
      if sum > j - i + 1 {
        break;
      }
    }
  }
// impl-end
}
