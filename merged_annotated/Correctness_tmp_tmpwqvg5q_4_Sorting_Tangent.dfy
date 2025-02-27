method Tangent(r: array<int>, x: array<int>) returns (found: bool)
  // pre-conditions-start
  requires forall i :: 1 <= i < x.Length ==> x[i - 1] < x[i]
  requires forall i, j :: 0 <= i < j < x.Length ==> x[i] < x[j]
  // pre-conditions-end
  // post-conditions-start
  ensures !found ==> forall i, j :: 0 <= i < r.Length && 0 <= j < x.Length ==> r[i] != x[j]
  ensures found ==> exists i, j :: 0 <= i < r.Length && 0 <= j < x.Length && r[i] == x[j]
  // post-conditions-end
{
// impl-start
  found := false;
  var n, f := 0, x.Length;
  while n != r.Length && !found
    // invariants-start

    invariant 0 <= n <= r.Length
    invariant !found ==> forall i, j :: 0 <= i < n && 0 <= j < x.Length ==> r[i] != x[j]
    invariant found ==> exists i, j :: 0 <= i < r.Length && 0 <= j < x.Length && n == i && f == j && r[i] == x[j]
    decreases r.Length - n, !found
    // invariants-end

  {
    f := BinarySearch(x, r[n]);
    if f != x.Length && r[n] == x[f] {
      found := true;
    } else {
      n := n + 1;
    }
  }
  // assert-start
  assert (!found && n == r.Length) || (found && n != r.Length && r[n] == x[f]);
  // assert-end

  // assert-start
  assert !false;
  // assert-end

// impl-end
}

method BinarySearch(a: array<int>, circle: int) returns (n: int)
  // pre-conditions-start
  requires forall i :: 1 <= i < a.Length ==> a[i - 1] < a[i]
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= n <= a.Length
  ensures forall i :: 0 <= i < n ==> a[i] < circle
  ensures forall i :: n <= i < a.Length ==> circle <= a[i]
  // post-conditions-end
{
// impl-start
  var lo, hi := 0, a.Length;
  while lo < hi
    // invariants-start

    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < circle
    invariant forall i :: hi <= i < a.Length ==> a[i] >= circle
    decreases hi - lo
    // invariants-end

  {
    var mid := (lo + hi) / 2;
    calc {
      lo;
    ==
      (lo + lo) / 2;
    <=
      {
        assert lo <= hi;
      }
      (lo + hi) / 2;
    <
      {
        assert lo < hi;
      }
      (hi + hi) / 2;
    ==
      hi;
    }
    if a[lo] > circle {
      hi := lo;
    } else if a[hi - 1] < circle {
      lo := hi;
    } else if a[mid] < circle {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  n := lo;
  // assert-start
  assert !false;
  // assert-end

// impl-end
}
