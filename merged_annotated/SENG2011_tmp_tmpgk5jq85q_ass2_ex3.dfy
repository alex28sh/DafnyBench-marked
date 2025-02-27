function sortedbad(s: string): bool
{
  forall i, j :: 
    0 <= i < |s| &&
    0 <= j < |s| &&
    s[i] == 'b' &&
    (s[j] == 'a' || s[j] == 'd') ==>
      i < j &&
      forall i, j :: 
        0 <= i < |s| &&
        0 <= j < |s| &&
        s[i] == 'a' &&
        s[j] == 'b' ==>
          i > j &&
          forall i, j :: 
            0 <= i < |s| &&
            0 <= j < |s| &&
            s[i] == 'a' &&
            s[j] == 'd' ==>
              i < j &&
              forall i, j :: 
                0 <= i < |s| &&
                0 <= j < |s| &&
                s[i] == 'd' &&
                (s[j] == 'a' || s[j] == 'b') ==>
                  i > j
}
// pure-end

method BadSort(a: string) returns (b: string)
  // pre-conditions-start
  requires forall k :: 0 <= k < |a| ==> a[k] == 'b' || a[k] == 'a' || a[k] == 'd'
  // pre-conditions-end
  // post-conditions-start
  ensures sortedbad(b)
  ensures multiset(a[..]) == multiset(b[..])
  ensures |a| == |b|
  // post-conditions-end
{
// impl-start
  b := a;
  var next := 0;
  var white := 0;
  var blue := |b|;
  while next != blue
    // invariants-start

    invariant forall k :: 0 <= k < |b| ==> b[k] == 'b' || b[k] == 'a' || b[k] == 'd'
    invariant 0 <= white <= next <= blue <= |b|
    invariant forall i :: 0 <= i < white ==> b[i] == 'b'
    invariant forall i :: white <= i < next ==> b[i] == 'a'
    invariant forall i :: blue <= i < |b| ==> b[i] == 'd'
    invariant forall i, j :: 0 <= i < next && 0 <= j < next && b[i] == 'b' && (b[j] == 'a' || b[j] == 'd') ==> i < j
    invariant forall i, j :: 0 <= i < next && 0 <= j < next && b[i] == 'a' && b[j] == 'b' ==> i > j
    invariant forall i, j :: 0 <= i < next && 0 <= j < next && b[i] == 'a' && b[j] == 'd' ==> i < j
    invariant forall i, j :: 0 <= i < next && 0 <= j < next && b[i] == 'd' && (b[j] == 'a' || b[j] == 'b') ==> i > j
    invariant multiset(b[..]) == multiset(a[..])
    invariant |a| == |b|
    // invariants-end

  {
    if b[next] == 'b' {
      var tmp := b[next];
      b := b[next := b[white]];
      b := b[white := tmp];
      next := next + 1;
      white := white + 1;
    } else if b[next] == 'a' {
      next := next + 1;
    } else if b[next] == 'd' {
      blue := blue - 1;
      var tmp := b[next];
      b := b[next := b[blue]];
      b := b[blue := tmp];
    }
  }
// impl-end
}

method check()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var f: string := "dabdabdab";
  var g: string := BadSort(f);
  // assert-start
  assert multiset(f) == multiset(g);
  // assert-end

  // assert-start
  assert sortedbad(g);
  // assert-end

// impl-end
}
