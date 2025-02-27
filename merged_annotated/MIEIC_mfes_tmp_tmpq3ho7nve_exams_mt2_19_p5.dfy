method partition(a: array<T>) returns (pivotPos: int)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures 0 <= pivotPos < a.Length
  ensures forall i :: 0 <= i < pivotPos ==> a[i] < a[pivotPos]
  ensures forall i :: pivotPos < i < a.Length ==> a[i] >= a[pivotPos]
  ensures multiset(a[..]) == multiset(old(a[..]))
  // post-conditions-end
{
// impl-start
  pivotPos := a.Length - 1;
  var i := 0;
  var j := 0;
  while j < a.Length - 1
    // invariants-start

    invariant 0 <= i <= j < a.Length
    invariant forall k :: 0 <= k < i ==> a[k] < a[pivotPos]
    invariant forall k :: i <= k < j ==> a[k] >= a[pivotPos]
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases a.Length - 1 - j
    // invariants-end

  {
    if a[j] < a[pivotPos] {
      a[i], a[j] := a[j], a[i];
      i := i + 1;
    }
    j := j + 1;
  }
  a[a.Length - 1], a[i] := a[i], a[a.Length - 1];
  pivotPos := i;
// impl-end
}

type T = int
