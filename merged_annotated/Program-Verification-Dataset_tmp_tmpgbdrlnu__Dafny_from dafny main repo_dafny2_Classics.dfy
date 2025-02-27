function Factorial(n: nat): nat
{
  if n == 0 then
    1
  else
    n * Factorial(n - 1)
}
// pure-end

method AdditiveFactorial(n: nat) returns (u: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures u == Factorial(n)
  // post-conditions-end
{
// impl-start
  u := 1;
  var r := 0;
  while r < n
    // invariants-start

    invariant 0 <= r <= n
    invariant u == Factorial(r)
    // invariants-end

  {
    var v := u;
    var s := 1;
    while s <= r
      // invariants-start

      invariant 1 <= s <= r + 1
      invariant u == s * Factorial(r)
      // invariants-end

    {
      u := u + v;
      s := s + 1;
    }
    r := r + 1;
  }
// impl-end
}

method FIND(A: array<int>, N: int, f: int)
  // pre-conditions-start
  requires A.Length == N
  requires 0 <= f < N
  // pre-conditions-end
  // post-conditions-start
  modifies A
  ensures forall p, q :: 0 <= p <= f <= q < N ==> A[p] <= A[q]
  // post-conditions-end
{
// impl-start
  var m, n := 0, N - 1;
  while m < n
    // invariants-start

    invariant 0 <= m <= f <= n < N
    invariant forall p, q :: 0 <= p < m <= q < N ==> A[p] <= A[q]
    invariant forall p, q :: 0 <= p <= n < q < N ==> A[p] <= A[q]
    // invariants-end

  {
    var r, i, j := A[f], m, n;
    while i <= j
      // invariants-start

      invariant m <= i && j <= n
      invariant -1 <= j && i <= N
      invariant i <= j ==> exists g :: i <= g < N && r <= A[g]
      invariant i <= j ==> exists g :: 0 <= g <= j && A[g] <= r
      invariant forall p :: 0 <= p < i ==> A[p] <= r
      invariant forall q :: j < q < N ==> r <= A[q]
      invariant forall p, q :: 0 <= p < m <= q < N ==> A[p] <= A[q]
      invariant forall p, q :: 0 <= p <= n < q < N ==> A[p] <= A[q]
      invariant (i == m && j == n && r == A[f]) || (m < i && j < n)
      // invariants-end

    {
      ghost var firstIteration := i == m && j == n;
      while A[i] < r
        // invariants-start

        invariant m <= i <= N && (firstIteration ==> i <= f)
        invariant exists g :: i <= g < N && r <= A[g]
        invariant exists g :: 0 <= g <= j && A[g] <= r
        invariant forall p :: 0 <= p < i ==> A[p] <= r
        decreases j - i
        // invariants-end

      {
        i := i + 1;
      }
      while r < A[j]
        // invariants-start

        invariant 0 <= j <= n && (firstIteration ==> f <= j)
        invariant exists g :: i <= g < N && r <= A[g]
        invariant exists g :: 0 <= g <= j && A[g] <= r
        invariant forall q :: j < q < N ==> r <= A[q]
        decreases j
        // invariants-end

      {
        j := j - 1;
      }
      // assert-start
      assert A[j] <= r <= A[i];
      // assert-end

      if i <= j {
        var w := A[i];
        A[i] := A[j];
        A[j] := w;
        // assert-start
        assert A[i] <= r <= A[j];
        // assert-end

        i, j := i + 1, j - 1;
      }
    }
    if f <= j {
      n := j;
    } else if i <= f {
      m := i;
    } else {
      break;
    }
  }
// impl-end
}
