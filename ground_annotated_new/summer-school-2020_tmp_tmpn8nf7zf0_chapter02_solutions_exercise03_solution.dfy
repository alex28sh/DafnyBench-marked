function IsSorted(s: seq<int>): bool
{
  forall i :: 
    0 <= i < |s| - 1 ==>
      s[i] <= s[i + 1]
}
// pure-end

function SortSpec(input: seq<int>, output: seq<int>): bool
{
  IsSorted(output) &&
  multiset(output) == multiset(input)
}
// pure-end

method merge_sort(input: seq<int>) returns (output: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures SortSpec(input, output)
  // post-conditions-end
{
// impl-start
  if |input| <= 1 {
    output := input;
  } else {
    var pivotIndex := |input| / 2;
    var left := input[..pivotIndex];
    var right := input[pivotIndex..];
    var leftSorted := left;
    leftSorted := merge_sort(left);
    var rightSorted := right;
    rightSorted := merge_sort(right);
    output := merge(leftSorted, rightSorted);
    // assert-start
    assert left + right == input;
    // assert-end

  }
// impl-end
}

method merge(a: seq<int>, b: seq<int>) returns (output: seq<int>)
  // pre-conditions-start
  requires IsSorted(a)
  requires IsSorted(b)
  // pre-conditions-end
  // post-conditions-start
  ensures SortSpec(a + b, output)
  // post-conditions-end
{
// impl-start
  var ai := 0;
  var bi := 0;
  output := [];
  while ai < |a| || bi < |b|
    // invariants-start

    invariant 0 <= ai <= |a|
    invariant 0 <= bi <= |b|
    invariant 0 < |output| && ai < |a| ==> output[|output| - 1] <= a[ai]
    invariant 0 < |output| && bi < |b| ==> output[|output| - 1] <= b[bi]
    invariant forall i :: 0 <= i < |output| - 1 ==> output[i] <= output[i + 1]
    invariant multiset(output) == multiset(a[..ai]) + multiset(b[..bi])
    decreases |a| - ai + |b| - bi
    // invariants-end

  {
    ghost var outputo := output;
    ghost var ao := ai;
    ghost var bo := bi;
    if ai == |a| || (bi < |b| && a[ai] > b[bi]) {
      output := output + [b[bi]];
      bi := bi + 1;
      // assert-start
      assert b[bo .. bi] == [b[bo]];
      // assert-end

    } else {
      output := output + [a[ai]];
      ai := ai + 1;
      // assert-start
      assert a[ao .. ai] == [a[ao]];
      // assert-end

    }
    // assert-start
    assert a[..ai] == a[..ao] + a[ao .. ai];
    // assert-end

    // assert-start
    assert b[..bi] == b[..bo] + b[bo .. bi];
    // assert-end

  }
  // assert-start
  assert a == a[..ai];
  // assert-end

  // assert-start
  assert b == b[..bi];
  // assert-end

// impl-end
}

method fast_sort(input: seq<int>) returns (output: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  output := [1, 2, 3];
// impl-end
}
