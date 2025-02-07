method ArrayToSeq(a: array<int>) returns (s: seq<int>)
  // pre-conditions-start
  requires a != null
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == a.Length
  ensures forall i :: 0 <= i < a.Length ==> s[i] == a[i]
  // post-conditions-end
{
// impl-start
  s := [];
  for i := 0 to a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant |s| == i
    invariant forall j :: 0 <= j < i ==> s[j] == a[j]
    // invariants-end

  {
    s := s + [a[i]];
  }
// impl-end
}
