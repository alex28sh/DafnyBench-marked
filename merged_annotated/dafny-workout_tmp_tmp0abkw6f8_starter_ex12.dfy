method FindMax(a: array<int>) returns (max_idx: nat)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= max_idx < a.Length
  ensures forall j :: 0 <= j < a.Length ==> a[max_idx] >= a[j]
  // post-conditions-end
{
// impl-start
  max_idx := 0;
  var i: nat := 1;
  while i < a.Length
    // invariants-start

    invariant 1 <= i <= a.Length
    invariant 0 <= max_idx < i
    invariant forall j :: 0 <= j < i ==> a[max_idx] >= a[j]
    decreases a.Length - i
    // invariants-end

  {
    if a[i] > a[max_idx] {
      max_idx := i;
    }
    i := i + 1;
  }
  return max_idx;
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var arr: array<int> := new int[] [1, 1, 25, 7, 2, -2, 3, 3, 20];
  var idx := FindMax(arr);
  // assert-start
  assert forall i :: 0 <= i < arr.Length ==> arr[idx] >= arr[i];
  // assert-end

// impl-end
}
