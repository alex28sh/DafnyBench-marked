// Workshop_tmp_tmp0cu11bdq_Lecture_Answers_selection_sort.dfy

predicate sorted(a: array<int>)
  requires a != null
  reads a
{
  sorted'(a, a.Length)
}
// pure-end

predicate sorted'(a: array<int>, i: int)
  requires a != null
  requires 0 <= i <= a.Length
  reads a
{
  forall k :: 
    0 < k < i ==>
      a[k - 1] <= a[k]
}
// pure-end

method SelectionSort(a: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures sorted(a)
  // post-conditions-end
{
// impl-start
  var n := 0;
  while n != a.Length
    // invariants-start

    invariant 0 <= n <= a.Length
    invariant forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
    invariant forall k1, k2 :: 0 <= k1 < k2 < n ==> a[k1] <= a[k2]
    // invariants-end

  {
    var mindex := n;
    var m := n + 1;
    while m != a.Length
      // invariants-start

      invariant n <= m <= a.Length
      invariant n <= mindex < m <= a.Length
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
      // invariants-end

    {
      if a[m] < a[mindex] {
        mindex := m;
      }
      m := m + 1;
    }
    a[n], a[mindex] := a[mindex], a[n];
    n := n + 1;
  }
// impl-end
}
