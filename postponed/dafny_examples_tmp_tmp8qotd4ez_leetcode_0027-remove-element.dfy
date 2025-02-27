
method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies nums
  ensures 0 <= newLength <= nums.Length
  ensures forall x :: x in nums[..newLength] ==> x != val
  ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
  // post-conditions-end
{
// impl-start
  var i := 0;
  var j := 0;
  while i < nums.Length
    // invariants-start

    invariant j <= i
    invariant i <= nums.Length
    invariant old(nums[i..]) == nums[i..]
    invariant multiset(nums[..j]) == multiset(old(nums[..i]))[val := 0]
    // invariants-end

  {
    if nums[i] != val {
      nums[j] := nums[i];
      j := j + 1;
    }
    i := i + 1;
  }
  // assert-start
  assert old(nums[..i]) == old(nums[..]);
  // assert-end

  return j;
// impl-end
}
