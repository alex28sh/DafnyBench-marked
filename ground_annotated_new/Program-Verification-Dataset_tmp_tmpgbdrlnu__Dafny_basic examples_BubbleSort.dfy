function sorted(a: array<int>, from: int, to: int): bool
  requires a != null
  requires 0 <= from <= to <= a.Length
  reads a
{
  forall u, v :: 
    from <= u < v < to ==>
      a[u] <= a[v]
}
// pure-end

function pivot(a: array<int>, to: int, pvt: int): bool
  requires a != null
  requires 0 <= pvt < to <= a.Length
  reads a
{
  forall u, v :: 
    0 <= u < pvt < v < to ==>
      a[u] <= a[v]
}
// pure-end

method bubbleSort(a: array<int>)
  // pre-conditions-start
  requires a != null && a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures sorted(a, 0, a.Length)
  ensures multiset(a[..]) == multiset(old(a[..]))
  // post-conditions-end
{
// impl-start
  var i: nat := 1;
  while i < a.Length
    // invariants-start

    invariant i <= a.Length
    invariant sorted(a, 0, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
    // invariants-end

  {
    var j: nat := i;
    while j > 0
      // invariants-start

      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant sorted(a, 0, j)
      invariant sorted(a, j, i + 1)
      invariant pivot(a, i + 1, j)
      // invariants-end

    {
      if a[j - 1] > a[j] {
        var temp: int := a[j - 1];
        a[j - 1] := a[j];
        a[j] := temp;
      }
      j := j - 1;
    }
    i := i + 1;
  }
// impl-end
}
