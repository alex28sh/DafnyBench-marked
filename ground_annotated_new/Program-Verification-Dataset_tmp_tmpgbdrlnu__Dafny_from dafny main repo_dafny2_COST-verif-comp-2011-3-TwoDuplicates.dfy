function IsDuplicate(a: array<int>, p: int): bool
  reads a
{
  IsPrefixDuplicate(a, a.Length, p)
}
// pure-end

function IsPrefixDuplicate(a: array<int>, k: int, p: int): bool
  requires 0 <= k <= a.Length
  reads a
{
  exists i, j :: 
    0 <= i < j < k &&
    a[i] == a[j] == p
}
// pure-end

method Search(a: array<int>) returns (p: int, q: int)
  // pre-conditions-start
  requires 4 <= a.Length
  requires exists p, q :: p != q && IsDuplicate(a, p) && IsDuplicate(a, q)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i] < a.Length - 2
  // pre-conditions-end
  // post-conditions-start
  ensures p != q && IsDuplicate(a, p) && IsDuplicate(a, q)
  // post-conditions-end
{
// impl-start
  var d := new int[a.Length - 2];
  var i := 0;
  while i < d.Length
    // invariants-start

    invariant 0 <= i <= d.Length && forall j :: 0 <= j < i ==> d[j] == -1
    // invariants-end

  {
    d[i], i := -1, i + 1;
  }
  i, p, q := 0, 0, 1;
  while true
    // invariants-start

    invariant 0 <= i < a.Length
    invariant forall j :: 0 <= j < d.Length ==> (d[j] == -1 && forall k :: 0 <= k < i ==> a[k] != j) || (0 <= d[j] < i && a[d[j]] == j)
    invariant p == q ==> IsDuplicate(a, p)
    invariant forall k {:trigger old(a[k])} :: 0 <= k < i && IsPrefixDuplicate(a, i, a[k]) ==> p == q == a[k]
    decreases a.Length - i
    // invariants-end

  {
    var k := d[a[i]];
    // assert-start
    assert k < i;
    // assert-end

    if k == -1 {
      d[a[i]] := i;
    } else {
      // assert-start
      assert a[i] == a[k] && IsDuplicate(a, a[i]);
      // assert-end

      if p != q {
        p, q := a[i], a[i];
      } else if p == a[i] {
      } else {
        q := a[i];
        return;
      }
    }
    i := i + 1;
  }
// impl-end
}
