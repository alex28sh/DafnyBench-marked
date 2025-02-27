method flip(a: array<int>, num: int)
  // pre-conditions-start
  requires a.Length > 0
  requires 0 <= num < a.Length
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall k :: 0 <= k <= num ==> a[k] == old(a[num - k])
  ensures forall k :: num < k < a.Length ==> a[k] == old(a[k])
  // post-conditions-end
{
// impl-start
  var tmp: int;
  var i := 0;
  var j := num;
  while i < j
    // invariants-start

    invariant i + j == num
    invariant 0 <= i <= num / 2 + 1
    invariant num / 2 <= j <= num
    invariant forall n :: 0 <= n < i ==> a[n] == old(a[num - n])
    invariant forall n :: 0 <= n < i ==> a[num - n] == old(a[n])
    invariant forall k :: i <= k <= j ==> a[k] == old(a[k])
    invariant forall k :: num < k < a.Length ==> a[k] == old(a[k])
    decreases j
    // invariants-end

  {
    tmp := a[i];
    a[i] := a[j];
    a[j] := tmp;
    i := i + 1;
    j := j - 1;
  }
// impl-end
}
