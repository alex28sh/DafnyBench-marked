lemma M(a: seq<int>, m: map<bool, int>)
  // pre-conditions-start
  requires 2 <= |a|
  requires false in m && true in m
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  assume forall i {:trigger a[i]} :: 0 <= i < |a| - 1 ==> a[i] <= a[i + 1];
  var x :| 0 <= x <= |a| - 2;
  assert a[x] <= a[x + 1];
// impl-end
}
