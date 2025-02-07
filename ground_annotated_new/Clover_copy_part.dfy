method copy(src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat)
    returns (r: array<int>)
  // pre-conditions-start
  requires src.Length >= sStart + len
  requires dest.Length >= dStart + len
  // pre-conditions-end
  // post-conditions-start
  ensures r.Length == dest.Length
  ensures r[..dStart] == dest[..dStart]
  ensures r[dStart + len..] == dest[dStart + len..]
  ensures r[dStart .. len + dStart] == src[sStart .. len + sStart]
  // post-conditions-end
{
// impl-start
  if len == 0 {
    return dest;
  }
  var i: nat := 0;
  r := new int[dest.Length];
  while i < r.Length
    // invariants-start

    invariant i <= r.Length
    invariant r[..i] == dest[..i]
    // invariants-end

  {
    r[i] := dest[i];
    i := i + 1;
  }
  // assert-start
  assert r[..] == dest[..];
  // assert-end

  i := 0;
  while i < len
    // invariants-start

    invariant i <= len
    invariant r[..dStart] == dest[..dStart]
    invariant r[dStart + len..] == dest[dStart + len..]
    invariant r[dStart .. dStart + i] == src[sStart .. sStart + i]
    // invariants-end

  {
    // assert-start
    assert r[dStart + len..] == dest[dStart + len..];
    // assert-end

    r[dStart + i] := src[sStart + i];
    i := i + 1;
  }
// impl-end
}
