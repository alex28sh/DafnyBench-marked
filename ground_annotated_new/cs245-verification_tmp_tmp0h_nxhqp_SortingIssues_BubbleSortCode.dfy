method BubbleSort(A: array<int>, n: int)
  // pre-conditions-start
  requires A.Length >= 0 && n == A.Length
  // pre-conditions-end
  // post-conditions-start
  modifies A
  // post-conditions-end
{
// impl-start
  var i := 0;
  var j := 0;
  while i < n - 1
    // invariants-start

    // invariants-end
 {
    while j < n - i - 1
      // invariants-start

      // invariants-end
 {
      if A[j] < A[i] {
        var t := A[j];
        A[j] := A[i];
        A[i] := t;
      }
      j := j + 1;
    }
    i := i + 1;
  }
// impl-end
}
