method IsSmaller(a: seq<int>, b: seq<int>) returns (result: bool)
  // pre-conditions-start
  requires |a| == |b|
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> forall i :: 0 <= i < |a| ==> a[i] > b[i]
  ensures !result <==> exists i :: 0 <= i < |a| && a[i] <= b[i]
  // post-conditions-end
{
// impl-start
  result := true;
  for i := 0 to |a|
    // invariants-start

    invariant 0 <= i <= |a|
    invariant result <==> forall k :: 0 <= k < i ==> a[k] > b[k]
    invariant !result <==> exists k :: 0 <= k < i && a[k] <= b[k]
    // invariants-end

  {
    if a[i] <= b[i] {
      result := false;
      break;
    }
  }
// impl-end
}
