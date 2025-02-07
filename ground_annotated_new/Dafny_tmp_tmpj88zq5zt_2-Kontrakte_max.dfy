method max(a: array<int>, b: array<int>, i: int, j: int)
    returns (m: int)
  // pre-conditions-start
  requires 0 <= i < a.Length
  requires 0 <= j < b.Length
  // pre-conditions-end
  // post-conditions-start
  ensures a[i] > b[j] ==> m == a[i]
  ensures a[i] <= b[j] ==> m == b[j]
  // post-conditions-end
{
// impl-start
  if a[i] > b[j] {
    m := a[i];
  } else {
    m := b[j];
  }
// impl-end
}

method testMax(a: array<int>, b: array<int>, i: int, j: int)
  // pre-conditions-start
  requires 0 <= i < a.Length
  requires 0 <= j < b.Length
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var max := max(a, b, i, j);
  // assert-start
  assert a[i] > b[j] ==> max == a[i];
  // assert-end

  // assert-start
  assert a[i] <= b[j] ==> max == b[j];
  // assert-end

// impl-end
}
