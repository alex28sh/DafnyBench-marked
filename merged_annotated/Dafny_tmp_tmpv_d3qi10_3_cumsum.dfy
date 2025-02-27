function sum(a: array<int>, i: int): int
  requires 0 <= i < a.Length
  reads a
{
  a[i] + if i == 0 then 0 else sum(a, i - 1)
}
// pure-end

method cumsum(a: array<int>, b: array<int>)
  // pre-conditions-start
  requires a.Length == b.Length && a.Length > 0 && a != b
  // pre-conditions-end
  // post-conditions-start
  modifies b
  ensures forall i | 0 <= i < a.Length :: b[i] == sum(a, i)
  // post-conditions-end
{
// impl-start
  b[0] := a[0];
  var i := 1;
  while i < a.Length
    // invariants-start

    invariant 1 <= i <= a.Length
    invariant forall i' | 0 <= i' < i :: b[i'] == sum(a, i')
    // invariants-end

  {
    b[i] := b[i - 1] + a[i];
    i := i + 1;
  }
// impl-end
}
