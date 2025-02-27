method longestPrefix(a: array<int>, b: array<int>) returns (i: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures i <= a.Length && i <= b.Length
  ensures a[..i] == b[..i]
  ensures i < a.Length && i < b.Length ==> a[i] != b[i]
  // post-conditions-end
{
// impl-start
  i := 0;
  while i < a.Length && i < b.Length && a[i] == b[i]
    // invariants-start

    invariant i <= a.Length && i <= b.Length
    invariant a[..i] == b[..i]
    // invariants-end

  {
    i := i + 1;
  }
// impl-end
}

method testLongestPrefix()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new int[] [1, 3, 2, 4, 8];
  var b := new int[] [1, 3, 3, 4];
  var i := longestPrefix(a, b);
  // assert-start
  assert a[2] != b[2];
  // assert-end

  // assert-start
  assert i == 2;
  // assert-end

// impl-end
}
