method contains_duplicate(nums: seq<int>) returns (result: bool)
  // pre-conditions-start
  requires 1 <= |nums| <= 100000
  requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> distinct(nums)
  // post-conditions-end
{
// impl-start
  var i := 0;
  var s: set<int> := {};
  while i < |nums|
    // invariants-start

    invariant i <= |nums|
    invariant forall j :: j in nums[..i] <==> j in s
    invariant distinct(nums[..i])
    // invariants-end

  {
    var num := nums[i];
    if num in s {
      return false;
    }
    s := s + {num};
    i := i + 1;
  }
  return true;
// impl-end
}

function distinct(nums: seq<int>): bool
{
  forall i, j :: 
    0 <= i < j < |nums| ==>
      nums[i] != nums[j]
}
// pure-end
