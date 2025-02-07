method SearchRecursive(a: seq<int>, i: int, j: int, x: int)
    returns (k: int)
  // pre-conditions-start
  requires 0 <= i <= j <= |a|
  // pre-conditions-end
  // post-conditions-start
  ensures i <= k < j || k == -1
  ensures k != -1 ==> a[k] == x
  ensures k != -1 ==> forall r | k < r < j :: a[r] != x
  ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
  decreases j - i
  // post-conditions-end
{
// impl-start
  if j == i {
    k := -1;
    return;
  }
  if a[j - 1] == x {
    k := j - 1;
    return;
  } else {
    k := SearchRecursive(a, i, j - 1, x);
  }
// impl-end
}

method SearchLoop(a: seq<int>, i: int, j: int, x: int)
    returns (k: int)
  // pre-conditions-start
  requires 0 <= i <= j <= |a|
  // pre-conditions-end
  // post-conditions-start
  ensures i <= k < j || k == -1
  ensures k != -1 ==> a[k] == x
  ensures k != -1 ==> forall r | k < r < j :: a[r] != x
  ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
  // post-conditions-end
{
// impl-start
  if i == j {
    return -1;
  }
  var t := j;
  while t > i
    // invariants-start

    invariant forall p | t <= p < j :: a[p] != x
    decreases t
    // invariants-end

  {
    if a[t - 1] == x {
      k := t - 1;
      return;
    } else {
      t := t - 1;
    }
  }
  k := -1;
// impl-end
}
