method RemoveElement(s: array<int>, k: int) returns (v: array<int>)
  // pre-conditions-start
  requires 0 <= k < s.Length
  // pre-conditions-end
  // post-conditions-start
  ensures v.Length == s.Length - 1
  ensures forall i :: 0 <= i < k ==> v[i] == s[i]
  ensures forall i :: k <= i < v.Length ==> v[i] == s[i + 1]
  // post-conditions-end
{
// impl-start
  v := new int[s.Length - 1];
  var i := 0;
  while i < k
    // invariants-start

    invariant 0 <= i <= k
    invariant forall j :: 0 <= j < i ==> v[j] == s[j]
    // invariants-end

  {
    v[i] := s[i];
    i := i + 1;
  }
  // assert-start
  assert forall i :: 0 <= i < k ==> v[i] == s[i];
  // assert-end

  while i < v.Length
    // invariants-start

    invariant k <= i <= v.Length
    invariant forall j :: k <= j < i ==> v[j] == s[j + 1]
    invariant forall i :: 0 <= i < k ==> v[i] == s[i]
    // invariants-end

  {
    v[i] := s[i + 1];
    i := i + 1;
  }
// impl-end
}
