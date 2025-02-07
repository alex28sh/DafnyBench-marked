method RemoveDuplicates(nums: array<int>) returns (num_length: int)
  // pre-conditions-start
  requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
  // pre-conditions-end
  // post-conditions-start
  modifies nums
  ensures nums.Length == old(nums).Length
  ensures 0 <= num_length <= nums.Length
  ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
  ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
  ensures forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
  // post-conditions-end
{
// impl-start
  if nums.Length <= 1 {
    return nums.Length;
  }
  var last := 0;
  var i := 1;
  ghost var nums_before := nums[..];
  while i < nums.Length
    // invariants-start

    invariant 0 <= last < i <= nums.Length
    invariant nums[i..] == nums_before[i..]
    invariant forall j, k | 0 <= j < k <= last :: nums[j] < nums[k]
    invariant forall j | 0 <= j <= last :: nums[j] in nums_before[..i]
    invariant forall j | 0 <= j < i :: nums_before[j] in nums[..last + 1]
    // invariants-end

  {
    if nums[last] < nums[i] {
      last := last + 1;
      nums[last] := nums[i];
      // assert-start
      assert forall j | 0 <= j < i :: nums_before[j] in nums[..last];
      // assert-end

      // assert-start
      assert forall j | 0 <= j <= i :: nums_before[j] in nums[..last + 1];
      // assert-end

    }
    i := i + 1;
  }
  return last + 1;
// impl-end
}

method Testing()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var nums1 := new int[3];
  nums1[0] := 1;
  nums1[1] := 1;
  nums1[2] := 2;
  var num_length1 := RemoveDuplicates(nums1);
  // assert-start
  assert forall i, j | 0 <= i < j < num_length1 :: nums1[i] != nums1[j];
  // assert-end

  // assert-start
  assert num_length1 <= nums1.Length;
  // assert-end

  print "nums1: ", nums1[..], ", num_length1: ", num_length1, "\n";
  var nums2 := new int[10];
  nums2[0] := 0;
  nums2[1] := 0;
  nums2[2] := 1;
  nums2[3] := 1;
  nums2[4] := 1;
  nums2[5] := 2;
  nums2[6] := 2;
  nums2[7] := 3;
  nums2[8] := 3;
  nums2[9] := 4;
  var num_length2 := RemoveDuplicates(nums2);
  // assert-start
  assert forall i, j | 0 <= i < j < num_length1 :: nums1[i] != nums1[j];
  // assert-end

  // assert-start
  assert num_length2 <= nums2.Length;
  // assert-end

  print "nums2: ", nums2[..], ", num_length2: ", num_length2, "\n";
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  Testing();
// impl-end
}
