method swap(a: array<int>, i: nat, j: nat)
  // pre-conditions-start
  requires a != null && a.Length > 0 && i < a.Length && j < a.Length
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  // post-conditions-end
{
// impl-start
  a[i], a[j] := a[j], a[i];
// impl-end
}

method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
  // pre-conditions-start
  requires a != null && a.Length > 0 && lo < a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures lo <= minIdx < a.Length
  ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
  // post-conditions-end
{
// impl-start
  var j := lo;
  minIdx := lo;
  while j < a.Length
    // invariants-start

    invariant lo <= j <= a.Length
    invariant lo <= minIdx < a.Length
    invariant forall k :: lo <= k < j ==> a[k] >= a[minIdx]
    decreases a.Length - j
    // invariants-end

  {
    if a[j] < a[minIdx] {
      minIdx := j;
    }
    j := j + 1;
  }
// impl-end
}

function sorted(a: seq<int>): bool
{
  forall i | 0 < i < |a| :: 
    a[i - 1] <= a[i]
}
// pure-end

method selectionSort(a: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall k, l :: 0 <= k < i <= l < a.Length ==> a[k] <= a[l]
    invariant sorted(a[..i])
    // invariants-end

  {
    var mx := FindMin(a, i);
    a[i], a[mx] := a[mx], a[i];
    i := i + 1;
  }
// impl-end
}
