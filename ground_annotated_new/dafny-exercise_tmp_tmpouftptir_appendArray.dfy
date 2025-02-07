method appendArray(a: array<int>, b: array<int>) returns (c: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures c.Length == a.Length + b.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] == c[i]
  ensures forall i :: 0 <= i < b.Length ==> b[i] == c[a.Length + i]
  // post-conditions-end
{
// impl-start
  c := new int[a.Length + b.Length];
  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> c[j] == a[j]
    // invariants-end

  {
    c[i] := a[i];
    i := i + 1;
  }
  while i < b.Length + a.Length
    // invariants-start

    invariant a.Length <= i <= b.Length + a.Length
    invariant forall j :: 0 <= j < a.Length ==> a[j] == c[j]
    invariant forall j :: a.Length <= j < i ==> c[j] == b[j - a.Length]
    // invariants-end

  {
    c[i] := b[i - a.Length];
    i := i + 1;
  }
// impl-end
}
