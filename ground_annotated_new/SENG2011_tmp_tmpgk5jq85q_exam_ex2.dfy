method Getmini(a: array<int>) returns (mini: nat)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= mini < a.Length
  ensures forall x :: 0 <= x < a.Length ==> a[mini] <= a[x]
  ensures forall x :: 0 <= x < mini ==> a[mini] < a[x]
  // post-conditions-end
{
// impl-start
  var min: int := a[0];
  var i: int := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall x :: 0 <= x < i ==> min <= a[x]
    invariant min in a[..]
    // invariants-end

  {
    if a[i] < min {
      min := a[i];
    }
    i := i + 1;
  }
  var k: int := 0;
  while k < a.Length
    // invariants-start

    invariant 0 <= k <= a.Length
    invariant forall x :: 0 <= x < k ==> min < a[x]
    // invariants-end

  {
    if a[k] == min {
      return k;
    }
    k := k + 1;
  }
// impl-end
}
