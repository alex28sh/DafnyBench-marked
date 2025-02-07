function isSorted(a: array<real>, from: nat, to: nat): bool
  requires 0 <= from <= to <= a.Length
  reads a
{
  forall i, j :: 
    from <= i < j < to ==>
      a[i] <= a[j]
}
// pure-end

method selectionSort(a: array<real>)
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
  while i < a.Length - 1
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant isSorted(a, 0, i)
    invariant forall lhs, rhs :: 0 <= lhs < i <= rhs < a.Length ==> a[lhs] <= a[rhs]
    invariant multiset(a[..]) == multiset(old(a[..]))
    // invariants-end

  {
    var j := findMin(a, i, a.Length);
    a[i], a[j] := a[j], a[i];
    i := i + 1;
  }
// impl-end
}

method findMin(a: array<real>, from: nat, to: nat)
    returns (index: nat)
  // pre-conditions-start
  requires 0 <= from < to <= a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures from <= index < to
  ensures forall k :: from <= k < to ==> a[k] >= a[index]
  // post-conditions-end
{
// impl-start
  var i := from + 1;
  index := from;
  while i < to
    // invariants-start

    invariant from <= index < i <= to
    invariant forall k :: from <= k < i ==> a[k] >= a[index]
    decreases a.Length - i
    // invariants-end

  {
    if a[i] < a[index] {
      index := i;
    }
    i := i + 1;
  }
// impl-end
}

method testSelectionSort()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new real[5] [9.0, 4.0, 6.0, 3.0, 8.0];
  // assert-start
  assert a[..] == [9.0, 4.0, 6.0, 3.0, 8.0];
  // assert-end

  selectionSort(a);
  // assert-start
  assert a[..] == [3.0, 4.0, 6.0, 8.0, 9.0];
  // assert-end

// impl-end
}

method testFindMin()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new real[5] [9.0, 5.0, 6.0, 4.0, 8.0];
  var m := findMin(a, 0, 5);
  // assert-start
  assert a[3] == 4.0;
  // assert-end

  // assert-start
  assert m == 3;
  // assert-end

// impl-end
}
