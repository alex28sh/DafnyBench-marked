function sortedbad(s: string): bool
{
  forall i, j :: 
    0 <= i <= j < |s| &&
    s[i] == 'b' &&
    s[j] != 'b' ==>
      i < j &&
      forall i, j :: 
        0 <= i <= j < |s| &&
        s[i] != 'd' &&
        s[j] == 'd' ==>
          i < j
}
// pure-end

method BadSort(a: string) returns (b: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |a| ==> a[i] in {'b', 'a', 'd'}
  // pre-conditions-end
  // post-conditions-start
  ensures sortedbad(b)
  ensures multiset(b[..]) == multiset(a[..])
  // post-conditions-end
{
// impl-start
  b := a;
  var next: int := 0;
  var aPointer: int := 0;
  var dPointer: int := |b|;
  while next != dPointer
    // invariants-start

    invariant 0 <= aPointer <= next <= dPointer <= |b|
    invariant forall i :: 0 <= i < aPointer ==> b[i] == 'b'
    invariant forall i :: aPointer <= i < next ==> b[i] == 'a'
    invariant forall i :: dPointer <= i < |b| ==> b[i] == 'd'
    invariant forall i :: 0 <= i < |b| ==> b[i] in {'b', 'a', 'd'}
    invariant sortedbad(b)
    invariant multiset(b[..]) == multiset(a[..])
    decreases if next <= dPointer then dPointer - next else next - dPointer
    // invariants-end

  {
    if b[next] == 'a' {
      next := next + 1;
    } else if b[next] == 'b' {
      b := b[next := b[aPointer]][aPointer := b[next]];
      next := next + 1;
      aPointer := aPointer + 1;
    } else {
      dPointer := dPointer - 1;
      b := b[next := b[dPointer]][dPointer := b[next]];
    }
  }
// impl-end
}
