method Reverse(a: array<char>) returns (b: array<char>)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures a == old(a)
  ensures b.Length == a.Length
  ensures forall i :: 0 <= i < a.Length ==> b[i] == a[a.Length - i - 1]
  // post-conditions-end
{
// impl-start
  b := new char[a.Length];
  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> b[j] == a[a.Length - j - 1]
    // invariants-end

  {
    b[i] := a[a.Length - i - 1];
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
  var a := new char[] ['s', 'k', 'r', 'o', 'w', 't', 'i'];
  var b := Reverse(a);
  // assert-start
  assert b[..] == ['i', 't', 'w', 'o', 'r', 'k', 's'];
  // assert-end

  print b[..];
  a := new char[] ['!'];
  b := Reverse(a);
  // assert-start
  assert b[..] == a[..];
  // assert-end

  print b[..], '\n';
// impl-end
}
