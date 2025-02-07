method Tangent(r: array<int>, x: array<int>) returns (b: bool)
  // pre-conditions-start
  requires forall i, j :: 0 <= i <= j < x.Length ==> x[i] <= x[j]
  requires forall i, j :: 0 <= i < r.Length && 0 <= j < x.Length ==> r[i] >= 0 && x[j] >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures !b ==> forall i, j :: 0 <= i < r.Length && 0 <= j < x.Length ==> r[i] != x[j]
  ensures b ==> exists i, j :: 0 <= i < r.Length && 0 <= j < x.Length && r[i] == x[j]
  // post-conditions-end
{
// impl-start
  var tempB, tangentMissing, k, l := false, false, 0, 0;
  while k != r.Length && !tempB
    // invariants-start

    invariant 0 <= k <= r.Length
    invariant tempB ==> exists i, j :: 0 <= i < r.Length && 0 <= j < x.Length && r[i] == x[j]
    invariant !tempB ==> forall i, j :: 0 <= i < k && 0 <= j < x.Length ==> r[i] != x[j]
    decreases r.Length - k
    // invariants-end

  {
    l := 0;
    tangentMissing := false;
    while l != x.Length && !tangentMissing
      // invariants-start

      invariant 0 <= l <= x.Length
      invariant tempB ==> exists i, j :: 0 <= i < r.Length && 0 <= j < x.Length && r[i] == x[j]
      invariant !tempB ==> forall i :: 0 <= i < l ==> r[k] != x[i]
      invariant tangentMissing ==> forall i :: l <= i < x.Length ==> r[k] != x[i]
      decreases x.Length - l, !tempB, !tangentMissing
      // invariants-end

    {
      if r[k] == x[l] {
        tempB := true;
      }
      if r[k] < x[l] {
        tangentMissing := true;
      }
      l := l + 1;
    }
    k := k + 1;
  }
  b := tempB;
// impl-end
}
