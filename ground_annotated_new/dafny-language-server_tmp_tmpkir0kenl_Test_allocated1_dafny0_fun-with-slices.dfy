method seqIntoArray<A>(s: seq<A>, a: array<A>, index: nat)
  // pre-conditions-start
  requires index + |s| <= a.Length
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures a[..] == old(a[..index]) + s + old(a[index + |s|..])
  // post-conditions-end
{
// impl-start
  var i := index;
  while i < index + |s|
    // invariants-start

    invariant index <= i <= index + |s| <= a.Length
    invariant a[..] == old(a[..index]) + s[..i - index] + old(a[i..])
    // invariants-end

  {
    label A:
    a[i] := s[i - index];
    calc {
      a[..];
    ==
      old@A(a[..])[i := s[i - index]];
    ==
      (old(a[..index]) + s[..i - index] + old(a[i..]))[i := s[i - index]];
    ==
      {
        assert old(a[..index]) + s[..i - index] + old(a[i..]) == old(a[..index]) + s[..i - index] + old(a[i..]);
      }
      (old(a[..index]) + s[..i - index] + old(a[i..]))[i := s[i - index]];
    ==
      {
        assert |old(a[..index]) + s[..i - index]| == i;
      }
      old(a[..index]) + s[..i - index] + old(a[i..])[0 := s[i - index]];
    ==
      {
        assert old(a[i..])[0 := s[i - index]] == [s[i - index]] + old(a[i..])[1..];
      }
      old(a[..index]) + s[..i - index] + [s[i - index]] + old(a[i..])[1..];
    ==
      {
        assert old(a[i..])[1..] == old(a[i + 1..]);
      }
      old(a[..index]) + s[..i - index] + [s[i - index]] + old(a[i + 1..]);
    ==
      old(a[..index]) + (s[..i - index] + [s[i - index]]) + old(a[i + 1..]);
    ==
      {
        assert s[..i - index] + [s[i - index]] == s[..i + 1 - index];
      }
      old(a[..index]) + s[..i + 1 - index] + old(a[i + 1..]);
    }
    i := i + 1;
  }
// impl-end
}
