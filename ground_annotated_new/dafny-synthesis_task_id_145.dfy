method MaxDifference(a: array<int>) returns (diff: int)
  // pre-conditions-start
  requires a.Length > 1
  // pre-conditions-end
  // post-conditions-start
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
  // post-conditions-end
{
// impl-start
  var minVal := a[0];
  var maxVal := a[0];
  for i := 1 to a.Length
    // invariants-start

    invariant 1 <= i <= a.Length
    invariant minVal <= maxVal
    invariant forall k :: 0 <= k < i ==> minVal <= a[k] && a[k] <= maxVal
    // invariants-end

  {
    if a[i] < minVal {
      minVal := a[i];
    } else if a[i] > maxVal {
      maxVal := a[i];
    }
  }
  diff := maxVal - minVal;
// impl-end
}
