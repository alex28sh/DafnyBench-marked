method twoSum(nums: array<int>, target: int)
    returns (i: int, j: int)
  // pre-conditions-start
  requires nums.Length > 1
  requires exists i, j :: 0 <= i < j < nums.Length && nums[i] + nums[j] == target
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= i < j < nums.Length && nums[i] + nums[j] == target
  ensures forall ii, jj :: 0 <= ii < i && ii < jj < nums.Length ==> nums[ii] + nums[jj] != target
  ensures forall jj :: i < jj < j ==> nums[i] + nums[jj] != target
  // post-conditions-end
{
// impl-start
  var n := nums.Length;
  i := 0;
  j := 1;
  while i < n - 1
    // invariants-start

    invariant 0 <= i < j <= n
    invariant forall ii, jj :: 0 <= ii < i && ii < jj < n ==> nums[ii] + nums[jj] != target
    // invariants-end

  {
    j := i + 1;
    while j < n
      // invariants-start

      invariant 0 <= i < j <= n
      invariant forall jj :: i < jj < j ==> nums[i] + nums[jj] != target
      // invariants-end

    {
      if nums[i] + nums[j] == target {
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
// impl-end
}
