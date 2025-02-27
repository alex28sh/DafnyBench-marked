function sorted_between(a: array<int>, from: nat, to: nat): bool
  requires a != null
  requires from <= to
  requires to <= a.Length
  reads a
{
  forall i, j :: 
    from <= i < j < to &&
    0 <= i < j < a.Length ==>
      a[i] <= a[j]
}
// pure-end

function sorted(a: array<int>): bool
  requires a != null
  reads a
{
  sorted_between(a, 0, a.Length)
}
// pure-end

method bubbleSort(a: array<int>)
  // pre-conditions-start
  requires a != null
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures sorted(a)
  ensures multiset(old(a[..])) == multiset(a[..])
  // post-conditions-end
{
// impl-start
  var i: nat := 1;
  while i < a.Length
    // invariants-start

    invariant i <= a.Length
    invariant sorted_between(a, 0, i)
    invariant multiset(old(a[..])) == multiset(a[..])
    // invariants-end

  {
    var j: nat := i;
    while j > 0
      // invariants-start

      invariant 0 <= j <= i
      invariant sorted_between(a, 0, j)
      invariant forall u, v :: 0 <= u < j < v < i + 1 ==> a[u] <= a[v]
      invariant sorted_between(a, j, i + 1)
      invariant multiset(old(a[..])) == multiset(a[..])
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
