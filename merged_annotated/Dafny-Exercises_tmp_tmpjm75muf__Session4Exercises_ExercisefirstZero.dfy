method mfirstCero(v: array<int>) returns (i: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= i <= v.Length
  ensures forall j :: 0 <= j < i ==> v[j] != 0
  ensures i != v.Length ==> v[i] == 0
  // post-conditions-end
{
// impl-start
  i := 0;
  while i < v.Length && v[i] != 0
    // invariants-start

    invariant 0 <= i <= v.Length
    invariant forall j :: 0 <= j < i ==> v[j] != 0
    decreases v.Length - i
    // invariants-end

  {
    i := i + 1;
  }
// impl-end
}
