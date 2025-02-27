method leq(a: array<int>, b: array<int>) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> (a.Length <= b.Length && a[..] == b[..a.Length]) || exists k :: 0 <= k < a.Length && k < b.Length && a[..k] == b[..k] && a[k] < b[k]
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < a.Length && i < b.Length
    // invariants-start

    invariant 0 <= i <= a.Length && 0 <= i <= b.Length
    invariant a[..i] == b[..i]
    decreases a.Length - i
    // invariants-end

  {
    if a[i] < b[i] {
      return true;
    } else if a[i] > b[i] {
      return false;
    } else {
      i := i + 1;
    }
  }
  return a.Length <= b.Length;
// impl-end
}

method testLeq()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var b := new int[] [1, 2];
  var a1 := new int[] [];
  var r1 := leq(a1, b);
  // assert-start
  assert r1;
  // assert-end

  var a2 := new int[] [1];
  var r2 := leq(a2, b);
  // assert-start
  assert r2;
  // assert-end

  var a3 := new int[] [1, 2];
  var r3 := leq(a3, b);
  // assert-start
  assert r3;
  // assert-end

  var a4 := new int[] [1, 1, 2];
  var r4 := leq(a4, b);
  // assert-start
  assert a4[1] < b[1] && r4;
  // assert-end

  var a5 := new int[] [1, 2, 3];
  var r5 := leq(a5, b);
  // assert-start
  assert !r5;
  // assert-end

  var a6 := new int[] [2];
  var r6 := leq(a6, b);
  // assert-start
  assert !r6;
  // assert-end

// impl-end
}
