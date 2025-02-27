function sorted(a: array<int>, from: int, to: int): bool
  requires a != null
  requires 0 <= from <= to <= a.Length
  reads a
{
  forall x, y :: 
    from <= x < y < to ==>
      a[x] <= a[y]
}
// pure-end

function pivot(a: array<int>, to: int, pvt: int): bool
  requires a != null
  requires 0 <= pvt < to <= a.Length
  reads a
{
  forall x, y :: 
    0 <= x < pvt < y < to ==>
      a[x] <= a[y]
}
// pure-end

method BubbleSort(a: array<int>)
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
  var i := 1;
  while i < a.Length
    // invariants-start

    invariant i <= a.Length
    invariant sorted(a, 0, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
    // invariants-end

  {
    var j := i;
    while j > 0
      // invariants-start

      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant sorted(a, 0, j)
      invariant sorted(a, j, i + 1)
      invariant pivot(a, i + 1, j)
      // invariants-end

    {
      if a[j - 1] > a[j] {
        a[j - 1], a[j] := a[j], a[j - 1];
      }
      j := j - 1;
    }
    i := i + 1;
  }
// impl-end
}
