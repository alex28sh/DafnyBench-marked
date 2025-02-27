function sorted_between(A: array<int>, from: int, to: int): bool
  reads A
{
  forall i, j :: 
    0 <= i <= j < A.Length &&
    from <= i <= j <= to ==>
      A[i] <= A[j]
}
// pure-end

function sorted(A: array<int>): bool
  reads A
{
  sorted_between(A, 0, A.Length - 1)
}
// pure-end

method BubbleSort(A: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies A
  ensures sorted(A)
  ensures multiset(A[..]) == multiset(old(A[..]))
  // post-conditions-end
{
// impl-start
  var N := A.Length;
  var i := N - 1;
  while 0 < i
    // invariants-start

    invariant multiset(A[..]) == multiset(old(A[..]))
    invariant sorted_between(A, i, N - 1)
    invariant forall n, m :: 0 <= n <= i < m < N ==> A[n] <= A[m]
    decreases i
    // invariants-end

  {
    print A[..], "\n";
    var j := 0;
    while j < i
      // invariants-start

      invariant 0 < i < N
      invariant 0 <= j <= i
      invariant multiset(A[..]) == multiset(old(A[..]))
      invariant sorted_between(A, i, N - 1)
      invariant forall n, m :: 0 <= n <= i < m < N ==> A[n] <= A[m]
      invariant forall n :: 0 <= n <= j ==> A[n] <= A[j]
      decreases i - j
      // invariants-end

    {
      if A[j] > A[j + 1] {
        A[j], A[j + 1] := A[j + 1], A[j];
        print A[..], "\n";
      }
      j := j + 1;
    }
    i := i - 1;
    print "\n";
  }
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var A := new int[10];
  A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
  BubbleSort(A);
  print A[..];
// impl-end
}
