method CanyonSearch(a: array<int>, b: array<int>) returns (d: nat)
  // pre-conditions-start
  requires a.Length != 0 && b.Length != 0
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  requires forall i, j :: 0 <= i < j < b.Length ==> b[i] <= b[j]
  // pre-conditions-end
  // post-conditions-start
  ensures exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == if a[i] < b[j] then b[j] - a[i] else a[i] - b[j]
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> d <= if a[i] < b[j] then b[j] - a[i] else a[i] - b[j]
  // post-conditions-end
{
// impl-start
  var m, n := 0, 0;
  d := if a[0] < b[0] then b[0] - a[0] else a[0] - b[0];
  while m < a.Length && n < b.Length
    // invariants-start

    invariant 0 <= m <= a.Length && 0 <= n <= b.Length
    invariant exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && d == if a[i] < b[j] then b[j] - a[i] else a[i] - b[j]
    invariant forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> d <= (if a[i] < b[j] then b[j] - a[i] else a[i] - b[j]) || (m <= i && n <= j)
    decreases a.Length - m + b.Length - n
    // invariants-end

  {
    var t := if a[m] < b[n] then b[n] - a[m] else a[m] - b[n];
    d := if t < d then t else d;
    if
    case a[m] <= b[n] =>
      m := m + 1;
    case b[n] <= a[m] =>
      n := n + 1;
  }
// impl-end
}
