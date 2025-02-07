method Max(a: array<nat>) returns (m: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a.Length > 0 ==> forall k :: 0 <= k < a.Length ==> m >= a[k]
  ensures a.Length == 0 ==> m == -1
  ensures a.Length > 0 ==> m in a[..]
  // post-conditions-end
{
// impl-start
  if a.Length == 0 {
    return -1;
  }
  // assert-start
  assert a.Length > 0;
  // assert-end

  var i := 0;
  m := a[0];
  // assert-start
  assert m in a[..];
  // assert-end

  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> m >= a[k]
    invariant m in a[..]
    // invariants-end

  {
    if a[i] >= m {
      m := a[i];
    }
    i := i + 1;
  }
  // assert-start
  assert m in a[..];
  // assert-end

// impl-end
}

method Checker()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new nat[] [1, 2, 3, 50, 5, 51];
  var n := Max(a);
  // assert-start
  assert n == 51;
  // assert-end

// impl-end
}
