method GetEven(a: array<nat>)
  // pre-conditions-start
  requires true
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall i: int :: 0 <= i < a.Length ==> a[i] % 2 == 0
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length && forall j: int :: 0 <= j < i ==> a[j] % 2 == 0
    decreases a.Length - i
    // invariants-end

  {
    if a[i] % 2 != 0 {
      a[i] := a[i] + 1;
    }
    i := i + 1;
  }
// impl-end
}
