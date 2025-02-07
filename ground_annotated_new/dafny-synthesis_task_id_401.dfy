method IndexWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
  // pre-conditions-start
  requires |a| > 0 && |b| > 0
  requires |a| == |b|
  requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |a[i]|
  ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j]
  // post-conditions-end
{
// impl-start
  result := [];
  for i := 0 to |a|
    // invariants-start

    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |a[k]|
    invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < |result[k]| ==> result[k][j] == a[k][j] + b[k][j]
    // invariants-end

  {
    var subResult := [];
    for j := 0 to |a[i]|
      // invariants-start

      invariant 0 <= j <= |a[i]|
      invariant |subResult| == j
      invariant forall k :: 0 <= k < j ==> subResult[k] == a[i][k] + b[i][k]
      // invariants-end

    {
      subResult := subResult + [a[i][j] + b[i][j]];
    }
    result := result + [subResult];
  }
// impl-end
}
