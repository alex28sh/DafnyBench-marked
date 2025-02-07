method Reverse(a: array<char>) returns (b: array<char>)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures a.Length == b.Length
  ensures forall k :: 0 <= k < a.Length ==> b[k] == a[a.Length - 1 - k]
  // post-conditions-end
{
// impl-start
  b := new char[a.Length];
  // assert-start
  assert b.Length == a.Length;
  // assert-end

  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> b[k] == a[a.Length - 1 - k]
    // invariants-end

  {
    b[i] := a[a.Length - 1 - i];
    i := i + 1;
  }
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new char[8];
  a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7] := 'd', 'e', 's', 'r', 'e', 'v', 'e', 'r';
  var b := Reverse(a);
  // assert-start
  assert b[..] == ['r', 'e', 'v', 'e', 'r', 's', 'e', 'd'];
  // assert-end

  print b[..];
  a := new char[1];
  a[0] := '!';
  b := Reverse(a);
  // assert-start
  assert b[..] == ['!'];
  // assert-end

  print b[..], '\n';
// impl-end
}
