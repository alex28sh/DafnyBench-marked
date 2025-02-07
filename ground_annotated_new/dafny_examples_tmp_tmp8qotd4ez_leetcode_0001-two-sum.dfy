function InMap(nums: seq<int>, m: map<int, int>, t: int): bool
{
  forall j :: 
    0 <= j < |nums| ==>
      t - nums[j] in m
}
// pure-end

method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length && nums[r.0] + nums[r.1] == target && forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
  ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
  // post-conditions-end
{
// impl-start
  var m: map<int, int> := map[];
  var i := 0;
  while i < nums.Length
    // invariants-start

    invariant i <= nums.Length
    invariant forall k :: k in m ==> 0 <= m[k] < i
    invariant forall k :: k in m ==> nums[m[k]] + k == target
    invariant InMap(nums[..i], m, target)
    invariant forall u, v :: 0 <= u < v < i ==> nums[u] + nums[v] != target
    // invariants-end

  {
    if nums[i] in m {
      return (m[nums[i]], i);
    }
    m := m[target - nums[i] := i];
    i := i + 1;
  }
  return (-1, -1);
// impl-end
}
