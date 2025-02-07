method Difference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall x :: x in diff <==> x in a && x !in b
  ensures forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
  // post-conditions-end
{
// impl-start
  diff := [];
  for i := 0 to |a|
    // invariants-start

    invariant 0 <= i <= |a|
    invariant forall x :: x in diff <==> x in a[..i] && x !in b
    invariant forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
    // invariants-end

  {
    if a[i] !in b && a[i] !in diff {
      diff := diff + [a[i]];
    }
  }
// impl-end
}
