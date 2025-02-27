method rotate(a: array<int>, offset: int) returns (b: array<int>)
  // pre-conditions-start
  requires 0 <= offset
  // pre-conditions-end
  // post-conditions-start
  ensures b.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> b[i] == a[(i + offset) % a.Length]
  // post-conditions-end
{
// impl-start
  b := new int[a.Length];
  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> b[j] == a[(j + offset) % a.Length]
    // invariants-end

  {
    b[i] := a[(i + offset) % a.Length];
    i := i + 1;
  }
// impl-end
}
