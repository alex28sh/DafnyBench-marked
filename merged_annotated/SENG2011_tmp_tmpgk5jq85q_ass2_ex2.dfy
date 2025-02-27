function Sorted(a: string, low: int, high: int): bool
  requires 0 <= low <= high <= |a|
{
  forall j, k :: 
    low <= j < k < high ==>
      a[j] <= a[k]
}
// pure-end

method String3Sort(a: string) returns (b: string)
  // pre-conditions-start
  requires |a| == 3
  // pre-conditions-end
  // post-conditions-start
  ensures Sorted(b, 0, |b|)
  ensures |a| == |b|
  ensures multiset{b[0], b[1], b[2]} == multiset{a[0], a[1], a[2]}
  // post-conditions-end
{
// impl-start
  b := a;
  if b[0] > b[1] {
    b := b[0 := b[1]][1 := b[0]];
  }
  if b[1] > b[2] {
    b := b[1 := b[2]][2 := b[1]];
  }
  if b[0] > b[1] {
    b := b[0 := b[1]][1 := b[0]];
  }
// impl-end
}

method check()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a: string := "cba";
  var b: string := String3Sort(a);
  // assert-start
  assert b == "abc";
  // assert-end

  var a1: string := "aaa";
  var b1: string := String3Sort(a1);
  // assert-start
  assert b1 == "aaa";
  // assert-end

  var a2: string := "abc";
  var b2: string := String3Sort(a2);
  // assert-start
  assert b2 == "abc";
  // assert-end

  var a3: string := "cab";
  var b3: string := String3Sort(a3);
  // assert-start
  assert b3 == "abc";
  // assert-end

  var a4: string := "bac";
  var b4: string := String3Sort(a4);
  // assert-start
  assert b4 == "abc";
  // assert-end

  var a5: string := "bba";
  var b5: string := String3Sort(a5);
  // assert-start
  assert b5 == "abb";
  // assert-end

  var a6: string := "aba";
  var b6: string := String3Sort(a6);
  // assert-start
  assert b6 == "aab";
  // assert-end

  var a7: string := "acb";
  var b7: string := String3Sort(a7);
  // assert-start
  assert b7 == "abc";
  // assert-end

  var a8: string := "bca";
  var b8: string := String3Sort(a8);
  // assert-start
  assert b8 == "abc";
  // assert-end

  var a9: string := "bab";
  var b9: string := String3Sort(a9);
  // assert-start
  assert b9 == "abb";
  // assert-end

  var a10: string := "abb";
  var b10: string := String3Sort(a10);
  // assert-start
  assert b10 == "abb";
  // assert-end

// impl-end
}
