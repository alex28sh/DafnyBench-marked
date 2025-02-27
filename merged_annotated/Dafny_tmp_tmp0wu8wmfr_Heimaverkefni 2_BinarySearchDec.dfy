method SearchRecursive(a: seq<real>, i: int, j: int, x: real)
    returns (k: int)
  // pre-conditions-start
  requires 0 <= i <= j <= |a|
  requires forall p, q :: i <= p < q < j ==> a[p] >= a[q]
  // pre-conditions-end
  // post-conditions-start
  ensures i <= k <= j
  ensures forall r | i <= r < k :: a[r] >= x
  ensures forall r | k <= r < j :: a[r] < x
  decreases j - i
  // post-conditions-end
{
// impl-start
  if i == j {
    return i;
  }
  var m := i + (j - i) / 2;
  if a[m] < x {
    k := SearchRecursive(a, i, m, x);
  } else {
    k := SearchRecursive(a, m + 1, j, x);
  }
// impl-end
}

method SearchLoop(a: seq<real>, i: int, j: int, x: real)
    returns (k: int)
  // pre-conditions-start
  requires 0 <= i <= j <= |a|
  requires forall p, q :: i <= p < q < j ==> a[p] >= a[q]
  // pre-conditions-end
  // post-conditions-start
  ensures i <= k <= j
  ensures forall r | i <= r < k :: a[r] >= x
  ensures forall r | k <= r < j :: a[r] < x
  // post-conditions-end
{
// impl-start
  if i == j {
    return i;
  }
  var p := i;
  var q := j;
  while p != q
    // invariants-start

    invariant i <= p <= q <= j
    invariant forall r | i <= r < p :: a[r] >= x
    invariant forall r | q <= r < j :: a[r] < x
    decreases q - p
    // invariants-end

  {
    var m := p + (q - p) / 2;
    if a[m] < x {
      q := m;
    } else {
      p := m + 1;
    }
  }
  return p;
// impl-end
}

method Test(a: seq<real>, x: real)
  // pre-conditions-start
  requires forall p, q | 0 <= p < q < |a| :: a[p] >= a[q]
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var k1 := SearchLoop(a, 0, |a|, x);
  // assert-start
  assert forall r | 0 <= r < k1 :: a[r] >= x;
  // assert-end

  // assert-start
  assert forall r | k1 <= r < |a| :: a[r] < x;
  // assert-end

  var k2 := SearchRecursive(a, 0, |a|, x);
  // assert-start
  assert forall r | 0 <= r < k2 :: a[r] >= x;
  // assert-end

  // assert-start
  assert forall r | k2 <= r < |a| :: a[r] < x;
  // assert-end

// impl-end
}
