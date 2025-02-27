method PalVerify(a: array<char>) returns (yn: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures yn == true ==> forall i :: 0 <= i < a.Length / 2 ==> a[i] == a[a.Length - i - 1]
  ensures yn == false ==> exists i :: 0 <= i < a.Length / 2 && a[i] != a[a.Length - i - 1]
  ensures forall j :: 0 <= j < a.Length ==> a[j] == old(a[j])
  // post-conditions-end
{
// impl-start
  var i: int := 0;
  while i < a.Length / 2
    // invariants-start

    invariant 0 <= i <= a.Length / 2 && forall j :: 0 <= j < i ==> a[j] == a[a.Length - j - 1]
    decreases a.Length / 2 - i
    // invariants-end

  {
    if a[i] != a[a.Length - i - 1] {
      return false;
    }
    i := i + 1;
  }
  return true;
// impl-end
}

method TEST()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a: array<char> := new char[] ['r', 'e', 'f', 'e', 'r'];
  var r: bool := PalVerify(a);
  // assert-start
  assert r;
  // assert-end

  var b: array<char> := new char[] ['z'];
  r := PalVerify(b);
  // assert-start
  assert r;
  // assert-end

  var c: array<char> := new char[] [];
  r := PalVerify(c);
  // assert-start
  assert r;
  // assert-end

  var d: array<char> := new char[] ['x', 'y'];
  // assert-start
  assert d[0] == 'x' && d[1] == 'y';
  // assert-end

  r := PalVerify(d);
  // assert-start
  assert !r;
  // assert-end

  var e: array<char> := new char[] ['1', '2', '3', '4', '2', '1'];
  // assert-start
  assert e[0] == '1' && e[1] == '2' && e[2] == '3' && e[3] == '4' && e[4] == '2' && e[5] == '1';
  // assert-end

  r := PalVerify(e);
  // assert-start
  assert !r;
  // assert-end

// impl-end
}
