method concat(a: array<int>, b: array<int>) returns (c: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures c.Length == b.Length + a.Length
  ensures forall k :: 0 <= k < a.Length ==> c[k] == a[k]
  ensures forall k :: 0 <= k < b.Length ==> c[k + a.Length] == b[k]
  // post-conditions-end
{
// impl-start
  c := new int[a.Length + b.Length];
  var i := 0;
  while i < c.Length
    // invariants-start

    invariant 0 <= i <= c.Length
    invariant if i < a.Length then c[..i] == a[..i] else c[..i] == a[..] + b[..i - a.Length]
    // invariants-end

  {
    c[i] := if i < a.Length then a[i] else b[i - a.Length];
    i := i + 1;
  }
// impl-end
}
