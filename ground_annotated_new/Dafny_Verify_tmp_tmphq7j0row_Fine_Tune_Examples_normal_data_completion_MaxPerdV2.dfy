function contains(v: int, a: array<int>, n: int): bool
  requires n <= a.Length
  reads a
{
  exists j :: 
    0 <= j < n &&
    a[j] == v
}
// pure-end

function upper_bound(v: int, a: array<int>, n: int): bool
  requires n <= a.Length
  reads a
{
  forall j :: 
    0 <= j < n ==>
      a[j] <= v
}
// pure-end

function is_max(m: int, a: array<int>, n: int): bool
  requires n <= a.Length
  reads a
{
  contains(m, a, n) &&
  upper_bound(m, a, n)
}
// pure-end

method max(a: array<int>, n: int) returns (max: int)
  // pre-conditions-start
  requires 0 < n <= a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures is_max(max, a, n)
  // post-conditions-end
{
// impl-start
  var i: int := 1;
  max := a[0];
  while i < n
    // invariants-start

    invariant i <= n
    invariant is_max(max, a, i)
    // invariants-end

  {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
// impl-end
}
