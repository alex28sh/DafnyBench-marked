method findMax(a: array<real>) returns (max: real)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures exists k :: 0 <= k < a.Length && max == a[k]
  ensures forall k :: 0 <= k < a.Length ==> max >= a[k]
  // post-conditions-end
{
// impl-start
  max := a[0];
  for i := 1 to a.Length
    // invariants-start

    invariant exists k :: 0 <= k < i && max == a[k]
    invariant forall k :: 0 <= k < i ==> max >= a[k]
    // invariants-end

  {
    if a[i] > max {
      max := a[i];
    }
  }
// impl-end
}

method testFindMax()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a1 := new real[3] [1.0, 2.0, 3.0];
  var m1 := findMax(a1);
  // assert-start
  assert m1 == a1[2] == 3.0;
  // assert-end

  var a2 := new real[3] [3.0, 2.0, 1.0];
  var m2 := findMax(a2);
  // assert-start
  assert m2 == a2[0] == 3.0;
  // assert-end

  var a3 := new real[3] [2.0, 3.0, 1.0];
  var m3 := findMax(a3);
  // assert-start
  assert m3 == a3[1] == 3.0;
  // assert-end

  var a4 := new real[3] [1.0, 2.0, 2.0];
  var m4 := findMax(a4);
  // assert-start
  assert m4 == a4[1] == 2.0;
  // assert-end

  var a5 := new real[1] [1.0];
  var m5 := findMax(a5);
  // assert-start
  assert m5 == a5[0] == 1.0;
  // assert-end

  var a6 := new real[3] [1.0, 1.0, 1.0];
  var m6 := findMax(a6);
  // assert-start
  assert m6 == a6[0] == 1.0;
  // assert-end

// impl-end
}
