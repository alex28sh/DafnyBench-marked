method only_once<T(==)>(a: array<T>, key: T) returns (b: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures multiset(a[..])[key] == 1 <==> b
  // post-conditions-end
{
// impl-start
  var i := 0;
  b := false;
  var keyCount := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant multiset(a[..i])[key] == keyCount
    invariant b <==> keyCount == 1
    // invariants-end

  {
    if a[i] == key {
      keyCount := keyCount + 1;
    }
    if keyCount == 1 {
      b := true;
    } else {
      b := false;
    }
    i := i + 1;
  }
  // assert-start
  assert a[..a.Length] == a[..];
  // assert-end

// impl-end
}
