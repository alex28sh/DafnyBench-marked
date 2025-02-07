method Reverse(a: array<char>) returns (b: array<char>)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures a.Length == b.Length
  ensures forall x :: 0 <= x < a.Length ==> b[x] == a[a.Length - x - 1]
  // post-conditions-end
{
// impl-start
  b := new char[a.Length];
  var k := 0;
  while k < a.Length
    // invariants-start

    invariant 0 <= k <= a.Length
    invariant forall x :: 0 <= x < k ==> b[x] == a[a.Length - x - 1]
    decreases a.Length - k
    // invariants-end

  {
    b[k] := a[a.Length - 1 - k];
    k := k + 1;
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
