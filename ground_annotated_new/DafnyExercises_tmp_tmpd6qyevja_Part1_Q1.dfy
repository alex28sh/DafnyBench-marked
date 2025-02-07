method addArrays(a: array<int>, b: array<int>) returns (c: array<int>)
  // pre-conditions-start
  requires a.Length == b.Length
  // pre-conditions-end
  // post-conditions-start
  ensures b.Length == c.Length
  ensures forall i: int :: 0 <= i < c.Length ==> c[i] == a[i] + b[i]
  // post-conditions-end
{
// impl-start
  c := new int[a.Length];
  var j := 0;
  while j < a.Length
    // invariants-start

    invariant 0 <= j <= c.Length
    invariant forall i :: 0 <= i < j ==> c[i] == a[i] + b[i]
    // invariants-end

  {
    c[j] := a[j] + b[j];
    j := j + 1;
  }
// impl-end
}
