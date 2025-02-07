method sort(A: array<int>, n: int)
  // pre-conditions-start
  requires n == A.Length
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  modifies A
  ensures forall i, j :: 0 <= i <= j < n ==> A[i] <= A[j]
  // post-conditions-end
{
// impl-start
  var k := 0;
  while k < n
    // invariants-start

    invariant k <= n
    invariant forall i :: 0 <= i < k ==> A[i] == i
    // invariants-end

  {
    A[k] := k;
    k := k + 1;
  }
// impl-end
}
