twostate predicate Preserved(a: array<int>, left: nat, right: nat)
  requires left <= right <= a.Length
  reads a
{
  multiset(a[left .. right]) == multiset(old(a[left .. right]))
}
// pure-end

function Ordered(a: array<int>, left: nat, right: nat): bool
  requires left <= right <= a.Length
  reads a
{
  forall i: nat :: 
    0 < left <= i < right ==>
      a[i - 1] <= a[i]
}
// pure-end

twostate predicate Sorted(a: array<int>)
  reads a
{
  Ordered(a, 0, a.Length) &&
  Preserved(a, 0, a.Length)
}
// pure-end

method SelectionnSort(a: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures Sorted(a)
  // post-conditions-end
{
// impl-start
  for i := 0 to a.Length
    // invariants-start

    invariant Ordered(a, 0, i)
    invariant Preserved(a, 0, a.Length)
    // invariants-end

  {
    var minValue := a[i];
    var minPos := i;
    for j := i + 1 to a.Length
      // invariants-start

      invariant minPos < a.Length
      invariant a[minPos] == minValue
      // invariants-end

    {
      if a[j] < minValue {
        minValue := a[j];
        minPos := j;
      }
    }
    if i != minPos {
      a[i], a[minPos] := minValue, a[i];
    }
  }
// impl-end
}

method SelectionSort(a: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures Sorted(a)
  // post-conditions-end
{
// impl-start
  for i := 0 to a.Length
    // invariants-start

    invariant Ordered(a, 0, i)
    invariant Preserved(a, 0, a.Length)
    // invariants-end

  {
    ghost var minValue := a[i];
    for j := i + 1 to a.Length
      // invariants-start

      invariant a[i] == minValue
      invariant Preserved(a, 0, a.Length)
      // invariants-end

    {
      label L:
      // assert-start
      assert a[..] == old@L(a[..]);
      // assert-end

      if a[j] < minValue {
        minValue := a[j];
      }
      if a[j] < a[i] {
        // assert-start
        assert j != i;
        // assert-end

        a[i], a[j] := a[j], a[i];
      } else {
      }
    }
    // assert-start
    assert a[i] == minValue;
    // assert-end

  }
// impl-end
}
