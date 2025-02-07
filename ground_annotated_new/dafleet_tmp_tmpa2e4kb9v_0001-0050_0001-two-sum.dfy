function correct_pair(pair: (int, int), nums: seq<int>, target: int): bool
{
  var (i, j) := pair;
  0 <= i < |nums| &&
  0 <= j < |nums| &&
  i != j &&
  nums[i] + nums[j] == target
}
// pure-end

method twoSum(nums: seq<int>, target: int) returns (pair: (int, int))
  // pre-conditions-start
  requires exists i, j :: correct_pair((i, j), nums, target)
  // pre-conditions-end
  // post-conditions-start
  ensures correct_pair(pair, nums, target)
  // post-conditions-end
{
// impl-start
  var e_to_i := map[];
  for j := 0 to |nums|
    // invariants-start

    invariant forall i' | 0 <= i' < j :: nums[i'] in e_to_i
    invariant forall e | e in e_to_i :: 0 <= e_to_i[e] < j && nums[e_to_i[e]] == e
    invariant forall i', j' | i' < j && j' < j :: !correct_pair((i', j'), nums, target)
    // invariants-end

  {
    var element := nums[j];
    var rest := target - element;
    if rest in e_to_i {
      var i := e_to_i[rest];
      return (i, j);
    } else {
      e_to_i := e_to_i[element := j];
    }
  }
// impl-end
}
