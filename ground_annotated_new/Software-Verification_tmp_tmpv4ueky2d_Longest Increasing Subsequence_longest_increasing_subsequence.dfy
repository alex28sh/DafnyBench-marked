method longest_increasing_subsequence(nums: array<int>) returns (max: int)
  // pre-conditions-start
  requires 1 <= nums.Length <= 2500
  requires forall i :: 0 <= i < nums.Length ==> -10000 <= nums[i] <= 10000
  // pre-conditions-end
  // post-conditions-start
  ensures max >= 1
  // post-conditions-end
{
// impl-start
  var length := nums.Length;
  if length == 1 {
    return 1;
  }
  max := 1;
  var dp := new int[length] (_ /* _v0 */ => 1);
  var i := 1;
  while i < length
    // invariants-start

    invariant 1 <= i <= length
    invariant max >= 1
    modifies dp
    // invariants-end

  {
    var j := 0;
    while j < i
      // invariants-start

      invariant 0 <= j <= i
      // invariants-end

    {
      if nums[j] < nums[i] {
        dp[i] := find_max(dp[i], dp[j] + 1);
      }
      j := j + 1;
    }
    max := find_max(max, dp[i]);
    i := i + 1;
  }
// impl-end
}

function find_max(x: int, y: int): int
{
  if x > y then
    x
  else
    y
}
// pure-end
