method selectionSorted(Array: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
  // post-conditions-end
{
// impl-start
  var idx := 0;
  while idx < Array.Length
    // invariants-start

    invariant 0 <= idx <= Array.Length
    invariant forall i, j :: 0 <= i < idx <= j < Array.Length ==> Array[i] <= Array[j]
    invariant forall i, j :: 0 <= i < j < idx ==> Array[i] <= Array[j]
    invariant multiset(old(Array[..])) == multiset(Array[..])
    // invariants-end

  {
    var minIndex := idx;
    var idx' := idx + 1;
    while idx' < Array.Length
      // invariants-start

      invariant idx <= idx' <= Array.Length
      invariant idx <= minIndex < idx' <= Array.Length
      invariant forall k :: idx <= k < idx' ==> Array[minIndex] <= Array[k]
      // invariants-end

    {
      if Array[idx'] < Array[minIndex] {
        minIndex := idx';
      }
      idx' := idx' + 1;
    }
    Array[idx], Array[minIndex] := Array[minIndex], Array[idx];
    idx := idx + 1;
  }
// impl-end
}
