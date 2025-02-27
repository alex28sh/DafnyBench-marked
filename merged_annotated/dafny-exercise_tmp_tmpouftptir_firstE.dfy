method firstE(a: array<char>) returns (x: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1
  // post-conditions-end
{
// impl-start
  var i: int := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != 'e'
    // invariants-end

  {
    if a[i] == 'e' {
      return i;
    }
    i := i + 1;
  }
  return -1;
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a: array<char> := new char[] ['c', 'h', 'e', 'e', 's', 'e'];
  // assert-start
  assert a[0] == 'c' && a[1] == 'h' && a[2] == 'e';
  // assert-end

  var res := firstE(a);
  // assert-start
  assert res == 2;
  // assert-end

  a := new char[] ['e'];
  // assert-start
  assert a[0] == 'e';
  // assert-end

  res := firstE(a);
  // assert-start
  assert res == 0;
  // assert-end

  a := new char[] [];
  res := firstE(a);
  // assert-start
  assert res == -1;
  // assert-end

// impl-end
}
