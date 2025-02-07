function Below(c: Color, d: Color): bool
{
  c == Red || c == d || d == Blue
}
// pure-end

method DutchFlag(a: array<Color>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
  ensures multiset(a[..]) == multiset(old(a[..]))
  // post-conditions-end
{
// impl-start
  var r, w, b := 0, 0, a.Length;
  while w < b
    // invariants-start

    invariant 0 <= r <= w <= b <= a.Length
    invariant forall i :: 0 <= i < r ==> a[i] == Red
    invariant forall i :: r <= i < w ==> a[i] == White
    invariant forall i :: b <= i < a.Length ==> a[i] == Blue
    invariant multiset(a[..]) == multiset(old(a[..]))
    // invariants-end

  {
    match a[w]
    case {:split false} Red =>
      a[r], a[w] := a[w], a[r];
      r, w := r + 1, w + 1;
    case {:split false} White =>
      w := w + 1;
    case {:split false} Blue =>
      a[b - 1], a[w] := a[w], a[b - 1];
      b := b - 1;
  }
// impl-end
}

datatype Color = Red | White | Blue
