method InvertArray(a: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length - 1 - i])
  // post-conditions-end
{
// impl-start
  var index := 0;
  while index < a.Length / 2
    // invariants-start

    invariant 0 <= index <= a.Length / 2
    invariant forall i | 0 <= i < index :: a[i] == old(a[a.Length - 1 - i])
    invariant forall i | 0 <= i < index :: a[a.Length - 1 - i] == old(a[i])
    invariant forall i | index <= i < a.Length - index :: a[i] == old(a[i])
    // invariants-end

  {
    a[index], a[a.Length - 1 - index] := a[a.Length - 1 - index], a[index];
    index := index + 1;
  }
// impl-end
}
