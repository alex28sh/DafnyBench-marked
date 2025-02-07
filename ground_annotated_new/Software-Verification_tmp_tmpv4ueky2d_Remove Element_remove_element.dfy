method remove_element(nums: array<int>, val: int) returns (i: int)
  // pre-conditions-start
  requires 0 <= nums.Length <= 100
  requires forall i :: 0 <= i < nums.Length ==> 0 <= nums[i] <= 50
  requires 0 <= val <= 100
  // pre-conditions-end
  // post-conditions-start
  modifies nums
  ensures forall j :: 0 < j < i < nums.Length ==> nums[j] != val
  // post-conditions-end
{
// impl-start
  i := 0;
  var end := nums.Length - 1;
  while i <= end
    // invariants-start

    invariant 0 <= i <= nums.Length
    invariant end < nums.Length
    invariant forall k :: 0 <= k < i ==> nums[k] != val
    // invariants-end

  {
    if nums[i] == val {
      if nums[end] == val {
        end := end - 1;
      } else {
        nums[i] := nums[end];
        i := i + 1;
        end := end - 1;
      }
    } else {
      i := i + 1;
    }
  }
// impl-end
}
