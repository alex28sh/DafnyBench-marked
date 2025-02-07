function sorted(a: array?<int>, l: int, u: int): bool
  requires a != null
  reads a
{
  forall i, j :: 
    0 <= l <= i <= j <= u < a.Length ==>
      a[i] <= a[j]
}
// pure-end

function partitioned(a: array?<int>, i: int): bool
  requires a != null
  reads a
{
  forall k, k' :: 
    0 <= k <= i < k' < a.Length ==>
      a[k] <= a[k']
}
// pure-end

method BubbleSort(a: array?<int>)
  // pre-conditions-start
  requires a != null
  // pre-conditions-end
  // post-conditions-start
  modifies a
  // post-conditions-end
{
// impl-start
  var i := a.Length - 1;
  while i > 0
    // invariants-start

    invariant sorted(a, i, a.Length - 1)
    invariant partitioned(a, i)
    // invariants-end

  {
    var j := 0;
    while j < i
      // invariants-start

      invariant 0 < i < a.Length && 0 <= j <= i
      invariant sorted(a, i, a.Length - 1)
      invariant partitioned(a, i)
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
      // invariants-end

    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    i := i - 1;
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
  a[0], a[1], a[2], a[3], a[4] := 9, 4, 6, 3, 8;
  BubbleSort(a);
  var k := 0;
  while k < 5
    // invariants-start

    // invariants-end
 {
    print a[k], "\n";
    k := k + 1;
  }
// impl-end
}
