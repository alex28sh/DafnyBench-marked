method removeElement(nums: array<int>, val: int) returns (i: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies nums
  ensures forall k :: 0 < k < i < nums.Length ==> nums[k] != val
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
        nums[i], nums[end] := nums[end], nums[i];
        i := i + 1;
        end := end - 1;
      }
    } else {
      i := i + 1;
    }
  }
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var elems := new int[5] [1, 2, 3, 4, 5];
  var res := removeElement(elems, 5);
  print res, "\n", elems;
// impl-end
}
