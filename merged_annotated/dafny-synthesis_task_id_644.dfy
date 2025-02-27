method Reverse(a: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[a.Length - 1 - k])
  // post-conditions-end
{
// impl-start
  var l := a.Length - 1;
  var i := 0;
  while i < l - i
    // invariants-start

    invariant 0 <= i <= (l + 1) / 2
    invariant forall k :: 0 <= k < i || l - i < k <= l ==> a[k] == old(a[l - k])
    invariant forall k :: i <= k <= l - i ==> a[k] == old(a[k])
    // invariants-end

  {
    a[i], a[l - i] := a[l - i], a[i];
    i := i + 1;
  }
// impl-end
}

method ReverseUptoK(s: array<int>, k: int)
  // pre-conditions-start
  requires 2 <= k <= s.Length
  // pre-conditions-end
  // post-conditions-start
  modifies s
  ensures forall i :: 0 <= i < k ==> s[i] == old(s[k - 1 - i])
  ensures forall i :: k <= i < s.Length ==> s[i] == old(s[i])
  // post-conditions-end
{
// impl-start
  var l := k - 1;
  var i := 0;
  while i < l - i
    // invariants-start

    invariant 0 <= i <= (l + 1) / 2
    invariant forall p :: 0 <= p < i || l - i < p <= l ==> s[p] == old(s[l - p])
    invariant forall p :: i <= p <= l - i ==> s[p] == old(s[p])
    invariant forall p :: k <= p < s.Length ==> s[p] == old(s[p])
    // invariants-end

  {
    s[i], s[l - i] := s[l - i], s[i];
    i := i + 1;
  }
// impl-end
}
