function summingPair(i: nat, j: nat, nums: seq<int>, target: int): bool
  requires i < |nums|
  requires j < |nums|
{
  i != j &&
  nums[i] + nums[j] == target
}
// pure-end

method twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
  // pre-conditions-start
  requires exists i: nat, j: nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l < m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
  // post-conditions-end
{
// impl-start
  pair := (0, 0);
  var i: nat := 0;
  while i < |nums|
    // invariants-start

    invariant i <= |nums|
    invariant forall z: nat, j: nat :: 0 <= z < i && z + 1 <= j < |nums| ==> !summingPair(z, j, nums, target)
    // invariants-end

  {
    var k: nat := i + 1;
    while k < |nums|
      // invariants-start

      invariant i + 1 <= k <= |nums|
      invariant forall q: nat :: i + 1 <= q < k <= |nums| ==> !summingPair(i, q, nums, target)
      // invariants-end

    {
      if nums[i] + nums[k] == target {
        pair := (i, k);
        return pair;
      }
      k := k + 1;
    }
    i := i + 1;
  }
// impl-end
}
