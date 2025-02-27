// ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_Test_git-issues_git-issue-506.dfy

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new int[10];
  var index := 6;
  a[8] := 1;
  a[index], index := 3, index + 1;
  // assert-start
  assert a[6] == 3;
  // assert-end

  // assert-start
  assert index == 7;
  // assert-end

  print index, " ", a[6], a[7], a[8], "\n";
  index, a[index] := index + 1, 9;
  // assert-start
  assert index == 8;
  // assert-end

  // assert-start
  assert a[7] == 9;
  // assert-end

  // assert-start
  assert a[8] == 1;
  // assert-end

  // assert-start
  expect a[8] == 1;
  // assert-end

  print index, " ", a[6], a[7], a[8], "\n";
  a[index + 1], index := 7, 6;
  // assert-start
  assert a[9] == 7 && index == 6;
  // assert-end

  // assert-start
  expect a[9] == 7 && index == 6;
  // assert-end

  var o := new F(2);
  var oo := o;
  print o.f, " ", oo.f, "\n";
  // assert-start
  assert o.f == 2;
  // assert-end

  // assert-start
  assert oo.f == 2;
  // assert-end

  var ooo := new F(4);
  o.f, o := 5, ooo;
  print o.f, " ", oo.f, "\n";
  // assert-start
  assert o.f == 4;
  // assert-end

  // assert-start
  assert oo.f == 5;
  // assert-end

  var oooo := new F(6);
  o, o.f := oooo, 7;
  // assert-start
  assert o.f == 6;
  // assert-end

  // assert-start
  assert ooo.f == 7;
  // assert-end

  // assert-start
  expect ooo.f == 7;
  // assert-end

  print o.f, " ", ooo.f, "\n";
  var aa := new int[9, 9];
  var j := 4;
  var k := 5;
  aa[j, k] := 8;
  j, k, aa[j, k] := 2, 3, 7;
  print j, " ", k, " ", aa[4, 5], " ", aa[2, 3], "\n";
  // assert-start
  assert aa[4, 5] == 7;
  // assert-end

  // assert-start
  expect aa[4, 5] == 7;
  // assert-end

  j, aa[j, k], k := 5, 6, 1;
  // assert-start
  assert j == 5 && aa[2, 3] == 6 && k == 1;
  // assert-end

  // assert-start
  expect j == 5 && aa[2, 3] == 6 && k == 1;
  // assert-end

  aa[j, k], k, j := 5, 6, 1;
  // assert-start
  assert j == 1 && aa[5, 1] == 5 && k == 6;
  // assert-end

  // assert-start
  expect j == 1 && aa[5, 1] == 5 && k == 6;
  // assert-end

// impl-end
}

class F {
  var f: int

  constructor (f: int)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.f == f
    // post-conditions-end
  {
  // impl-start
    this.f := f;
  // impl-end
  }
}
