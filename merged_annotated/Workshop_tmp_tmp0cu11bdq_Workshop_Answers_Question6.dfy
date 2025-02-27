method arrayUpToN(n: int) returns (a: array<int>)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures a.Length == n
  ensures forall j :: 0 < j < n ==> a[j] >= 0
  ensures forall j, k: int :: 0 <= j <= k < n ==> a[j] <= a[k]
  // post-conditions-end
{
// impl-start
  var i := 0;
  a := new int[n];
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> a[k] >= 0
    invariant forall k :: 0 <= k < i ==> a[k] == k
    invariant forall j, k :: 0 <= j <= k < i ==> a[j] <= a[k]
    // invariants-end

  {
    a[i] := i;
    i := i + 1;
  }
// impl-end
}
