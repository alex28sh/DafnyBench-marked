function sorted(a: array<int>): bool
  reads a
{
  sortedA(a, a.Length)
}
// pure-end

function sortedA(a: array<int>, i: int): bool
  requires 0 <= i <= a.Length
  reads a
{
  forall k :: 
    0 < k < i ==>
      a[k - 1] <= a[k]
}
// pure-end

method lookForMin(a: array<int>, i: int) returns (m: int)
  // pre-conditions-start
  requires 0 <= i < a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures i <= m < a.Length
  ensures forall k :: i <= k < a.Length ==> a[k] >= a[m]
  // post-conditions-end
{
// impl-start
  var j := i;
  m := i;
  while j < a.Length
    // invariants-start

    invariant i <= j <= a.Length
    invariant i <= m < a.Length
    invariant forall k :: i <= k < j ==> a[k] >= a[m]
    decreases a.Length - j
    // invariants-end

  {
    if a[j] < a[m] {
      m := j;
    }
    j := j + 1;
  }
// impl-end
}

method insertionSort(a: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures sorted(a)
  // post-conditions-end
{
// impl-start
  var c := 0;
  while c < a.Length
    // invariants-start

    invariant 0 <= c <= a.Length
    invariant forall k, l :: 0 <= k < c <= l < a.Length ==> a[k] <= a[l]
    invariant sortedA(a, c)
    // invariants-end

  {
    var m := lookForMin(a, c);
    a[m], a[c] := a[c], a[m];
    // assert-start
    assert forall k :: c <= k < a.Length ==> a[k] >= a[c];
    // assert-end

    c := c + 1;
  }
// impl-end
}
