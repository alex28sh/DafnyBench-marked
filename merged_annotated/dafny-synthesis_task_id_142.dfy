method CountIdenticalPositions(a: seq<int>, b: seq<int>, c: seq<int>)
    returns (count: int)
  // pre-conditions-start
  requires |a| == |b| && |b| == |c|
  // pre-conditions-end
  // post-conditions-start
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i]|
  // post-conditions-end
{
// impl-start
  var identical := set i: int | 0 <= i < |a| && a[i] == b[i] && b[i] == c[i];
  count := |identical|;
// impl-end
}
