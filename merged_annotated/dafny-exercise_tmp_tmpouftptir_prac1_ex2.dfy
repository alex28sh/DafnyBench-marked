method Deli(a: array<char>, i: nat)
  // pre-conditions-start
  requires a.Length > 0
  requires 0 <= i < a.Length
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall j :: 0 <= j < i ==> a[j] == old(a[j])
  ensures forall j :: i <= j < a.Length - 1 ==> a[j] == old(a[j + 1])
  ensures a[a.Length - 1] == '.'
  // post-conditions-end
{
// impl-start
  var c := i;
  while c < a.Length - 1
    // invariants-start

    invariant i <= c <= a.Length - 1
    invariant forall j :: i <= j < c ==> a[j] == old(a[j + 1])
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[j])
    invariant forall j :: c <= j < a.Length ==> a[j] == old(a[j])
    // invariants-end

  {
    a[c] := a[c + 1];
    c := c + 1;
  }
  a[c] := '.';
// impl-end
}

method DeliChecker()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var z := new char[] ['b', 'r', 'o', 'o', 'm'];
  Deli(z, 1);
  // assert-start
  assert z[..] == "boom.";
  // assert-end

  Deli(z, 3);
  // assert-start
  assert z[..] == "boo..";
  // assert-end

  Deli(z, 4);
  // assert-start
  assert z[..] == "boo..";
  // assert-end

  Deli(z, 3);
  // assert-start
  assert z[..] == "boo..";
  // assert-end

  Deli(z, 0);
  Deli(z, 0);
  Deli(z, 0);
  // assert-start
  assert z[..] == ".....";
  // assert-end

  z := new char[] ['x'];
  Deli(z, 0);
  // assert-start
  assert z[..] == ".";
  // assert-end

// impl-end
}
