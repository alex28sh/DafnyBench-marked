method insertionSort(a: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures isSorted(a, 0, a.Length)
  ensures multiset(a[..]) == multiset(old(a[..]))
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant isSorted(a, 0, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
    decreases a.Length - i
    // invariants-end

  {
    var j := i;
    while j > 0 && a[j - 1] > a[j]
      // invariants-start

      invariant 0 <= j <= i
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant forall l, r :: 0 <= l < r <= i && r != j ==> a[l] <= a[r]
      decreases j
      // invariants-end

    {
      a[j - 1], a[j] := a[j], a[j - 1];
      j := j - 1;
    }
    i := i + 1;
  }
// impl-end
}

function isSorted(a: array<int>, from: nat, to: nat): bool
  requires 0 <= from <= to <= a.Length
  reads a
{
  forall i, j :: 
    from <= i < j < to ==>
      a[i] <= a[j]
}
// pure-end

method testInsertionSort()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new int[] [9, 4, 3, 6, 8];
  // assert-start
  assert a[..] == [9, 4, 3, 6, 8];
  // assert-end

  insertionSort(a);
  // assert-start
  assert a[..] == [3, 4, 6, 8, 9];
  // assert-end

// impl-end
}
