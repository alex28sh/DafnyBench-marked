method AbsIt(s: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies s
  ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
  ensures s.Length == old(s).Length
  // post-conditions-end
{
// impl-start
  var i: int := 0;
  while i < s.Length
    // invariants-start

    invariant 0 <= i <= s.Length
    invariant forall j :: 0 <= j < i ==> if old(s[j]) < 0 then s[j] == -old(s[j]) else s[j] == old(s[j])
    invariant forall j :: i <= j < s.Length ==> s[j] == old(s[j])
    // invariants-end

  {
    if s[i] < 0 {
      s[i] := -s[i];
    }
    i := i + 1;
  }
// impl-end
}

method Tester()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new int[] [-1, 2, -3, 4, -5, 6, -7, 8, -9];
  // assert-start
  assert a[0] == -1 && a[1] == 2 && a[2] == -3 && a[3] == 4 && a[4] == -5;
  // assert-end

  // assert-start
  assert a[5] == 6 && a[6] == -7 && a[7] == 8 && a[8] == -9;
  // assert-end

  AbsIt(a);
  // assert-start
  assert a[0] == 1 && a[1] == 2 && a[2] == 3 && a[3] == 4 && a[4] == 5;
  // assert-end

  // assert-start
  assert a[5] == 6 && a[6] == 7 && a[7] == 8 && a[8] == 9;
  // assert-end

  var b: array<int> := new int[] [-42, -2, -42, -2, -42, -2];
  // assert-start
  assert b[0] == -42 && b[1] == -2 && b[2] == -42;
  // assert-end

  // assert-start
  assert b[3] == -2 && b[4] == -42 && b[5] == -2;
  // assert-end

  AbsIt(b);
  // assert-start
  assert b[0] == 42 && b[1] == 2 && b[2] == 42;
  // assert-end

  // assert-start
  assert b[3] == 2 && b[4] == 42 && b[5] == 2;
  // assert-end

  var c: array<int> := new int[] [-1];
  // assert-start
  assert c[0] == -1;
  // assert-end

  AbsIt(c);
  // assert-start
  assert c[0] == 1;
  // assert-end

  var d: array<int> := new int[] [42];
  // assert-start
  assert d[0] == 42;
  // assert-end

  AbsIt(b);
  // assert-start
  assert d[0] == 42;
  // assert-end

  var e: array<int> := new int[] [];
  AbsIt(e);
  // assert-start
  assert e.Length == 0;
  // assert-end

// impl-end
}
