function sum(nums: seq<int>): int
{
  if |nums| == 0 then
    0
  else
    sum(nums[0 .. |nums| - 1]) + nums[|nums| - 1]
}
// pure-end

function sumUp(nums: seq<int>): int
{
  if |nums| == 0 then
    0
  else
    nums[0] + sumUp(nums[1..])
}
// pure-end

lemma sumUpLemma(a: seq<int>, b: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures sumUp(a + b) == sumUp(a) + sumUp(b)
  // post-conditions-end
{
// impl-start
  if a == [] {
    assert a + b == b;
  } else {
    sumUpLemma(a[1..], b);
    calc {
      sumUp(a + b);
      {
        assert (a + b)[0] == a[0];
        assert (a + b)[1..] == a[1..] + b;
      }
      a[0] + sumUp(a[1..] + b);
      a[0] + sumUp(a[1..]) + sumUp(b);
    }
  }
// impl-end
}

lemma sumsEqual(nums: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures sum(nums) == sumUp(nums)
  decreases |nums|
  // post-conditions-end
{
// impl-start
  if nums == [] {
  } else {
    var ln := |nums| - 1;
    calc {
      sumUp(nums[..]);
      {
        assert nums[..] == nums[0 .. ln] + [nums[ln]];
        sumUpLemma(nums[0 .. ln], [nums[ln]]);
      }
      sumUp(nums[0 .. ln]) + sumUp([nums[ln]]);
      {
        assert forall a :: sumUp([a]) == a;
      }
      sumUp(nums[0 .. ln]) + nums[ln];
      {
        sumsEqual(nums[0 .. ln]);
      }
      sum(nums[0 .. ln]) + nums[ln];
    }
  }
// impl-end
}

method FindPivotIndex(nums: seq<int>) returns (index: int)
  // pre-conditions-start
  requires |nums| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures index == -1 ==> forall k: nat :: k < |nums| ==> sum(nums[0 .. k]) != sum(nums[k + 1..])
  ensures 0 <= index < |nums| ==> sum(nums[0 .. index]) == sum(nums[index + 1..])
  // post-conditions-end
{
// impl-start
  var leftsums: seq<int> := [0];
  var rightsums: seq<int> := [0];
  var i := 1;
  // assert-start
  assert leftsums[0] == sum(nums[0 .. 0]);
  // assert-end

  // assert-start
  assert rightsums[0] == sumUp(nums[|nums|..]);
  // assert-end

  while i < |nums| + 1
    // invariants-start

    invariant 1 <= i <= |nums| + 1
    invariant |leftsums| == i
    invariant |rightsums| == i
    invariant forall k: nat :: 0 <= k < i && k <= |nums| ==> leftsums[k] == sum(nums[0 .. k])
    invariant forall k: nat :: 0 <= k < i && k <= |nums| ==> rightsums[k] == sumUp(nums[|nums| - k..])
    // invariants-end

  {
    leftsums := leftsums + [leftsums[i - 1] + nums[i - 1]];
    // assert-start
    assert nums[0 .. i] == nums[0 .. i - 1] + [nums[i - 1]];
    // assert-end

    rightsums := rightsums + [nums[|nums| - i] + rightsums[i - 1]];
    i := i + 1;
  }
  // assert-start
  assert forall k: nat :: 0 <= k < i && k <= |nums| ==> rightsums[k] == sum(nums[|nums| - k..]) by {
    forall k: nat | 0 <= k < i && k <= |nums|
      ensures sumUp(nums[|nums| - k..]) == sum(nums[|nums| - k..])
      ensures rightsums[k] == sumUp(nums[|nums| - k..])
    {
      sumsEqual(nums[|nums| - k..]);
    }
  }
  // assert-end

  i := 0;
  while i < |nums|
    // invariants-start

    invariant 0 <= i <= |nums|
    invariant forall k: nat :: k < i ==> sum(nums[0 .. k]) != sum(nums[k + 1..])
    // invariants-end

  {
    var x := |nums| - (i + 1);
    if leftsums[i] == rightsums[x] {
      // assert-start
      assert sum(nums[0 .. i]) == sum(nums[i + 1..]);
      // assert-end

      return i;
    }
    // assert-start
    assert sum(nums[0 .. i]) != sum(nums[i + 1..]);
    // assert-end

    i := i + 1;
  }
  return -1;
// impl-end
}
