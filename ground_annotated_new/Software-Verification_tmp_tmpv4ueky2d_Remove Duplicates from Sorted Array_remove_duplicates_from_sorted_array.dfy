method remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires is_sorted(nums)
  requires 1 <= |nums| <= 30000
  requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
  // pre-conditions-end
  // post-conditions-start
  ensures is_sorted_and_distinct(result)
  ensures forall i :: i in nums <==> i in result
  // post-conditions-end
{
// impl-start
  var previous := nums[0];
  result := [nums[0]];
  var i := 1;
  while i < |nums|
    // invariants-start

    invariant 0 <= i <= |nums|
    invariant |result| >= 1
    invariant previous in nums[0 .. i]
    invariant previous == result[|result| - 1]
    invariant is_sorted_and_distinct(result)
    invariant forall j :: j in nums[0 .. i] <==> j in result
    // invariants-end

  {
    if previous != nums[i] {
      result := result + [nums[i]];
      previous := nums[i];
    }
    i := i + 1;
  }
// impl-end
}

function is_sorted(nums: seq<int>): bool
{
  forall i, j :: 
    0 <= i < j < |nums| ==>
      nums[i] <= nums[j]
}
// pure-end

function is_sorted_and_distinct(nums: seq<int>): bool
{
  forall i, j :: 
    0 <= i < j < |nums| ==>
      nums[i] < nums[j]
}
// pure-end
