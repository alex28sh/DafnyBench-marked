method QuicksortPartition(X: array<int>, n: int, p: int)
    returns (a: int, b: int)
  // pre-conditions-start
  requires X.Length >= 1 && n == X.Length
  // pre-conditions-end
  // post-conditions-start
  modifies X
  ensures b >= n
  ensures forall x :: 0 <= x < a < n ==> X[x] <= p
  ensures forall x :: a == n || (0 <= a <= x < n ==> X[x] > p)
  ensures multiset(X[..]) == multiset(old(X[..]))
  // post-conditions-end
{
// impl-start
  a := 0;
  while a < n && X[a] <= p
    // invariants-start

    invariant 0 <= a <= n
    invariant forall x :: 0 <= x <= a - 1 ==> X[x] <= p
    // invariants-end

  {
    a := a + 1;
  }
  b := a + 1;
  while b < n
    // invariants-start

    invariant 0 <= a < b <= n + 1
    invariant b == n + 1 ==> a == n
    invariant forall x :: 0 <= x <= a - 1 ==> X[x] <= p
    invariant forall x :: a == n || (0 <= a <= x < b ==> X[x] > p)
    invariant multiset(X[..]) == multiset(old(X[..]))
    // invariants-end

  {
    if X[b] <= p {
      var t := X[b];
      X[b] := X[a];
      X[a] := t;
      a := a + 1;
    }
    b := b + 1;
  }
// impl-end
}
