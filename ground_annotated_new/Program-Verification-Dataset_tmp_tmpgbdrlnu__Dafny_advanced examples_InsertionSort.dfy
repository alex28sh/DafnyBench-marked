function sorted(a: array<int>, start: int, end: int): bool
  requires a != null
  requires 0 <= start <= end <= a.Length
  reads a
{
  forall j, k :: 
    start <= j < k < end ==>
      a[j] <= a[k]
}
// pure-end

method InsertionSort(a: array<int>)
  // pre-conditions-start
  requires a != null && a.Length > 1
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures sorted(a, 0, a.Length)
  // post-conditions-end
{
// impl-start
  var up := 1;
  while up < a.Length
    // invariants-start

    invariant 1 <= up <= a.Length
    invariant sorted(a, 0, up)
    // invariants-end

  {
    var down := up - 1;
    var temp := a[up];
    while down >= 0 && a[down + 1] < a[down]
      // invariants-start

      invariant forall j, k | 0 <= j < k < up + 1 && k != down + 1 :: a[j] <= a[k]
      // invariants-end

    {
      a[down], a[down + 1] := a[down + 1], a[down];
      down := down - 1;
    }
    up := up + 1;
  }
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 2, 5, 1, 8;
  InsertionSort(a);
  print a[..];
// impl-end
}
