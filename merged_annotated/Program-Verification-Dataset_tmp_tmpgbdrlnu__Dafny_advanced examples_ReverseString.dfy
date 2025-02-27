function reversed(arr: array<char>, outarr: array<char>): bool
  requires arr != null && outarr != null
  requires arr.Length == outarr.Length
  reads arr, outarr
{
  forall k :: 
    0 <= k <= arr.Length - 1 ==>
      outarr[k] == arr[arr.Length - 1 - k]
}
// pure-end

method yarra(arr: array<char>) returns (outarr: array<char>)
  // pre-conditions-start
  requires arr != null && arr.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures outarr != null && arr.Length == outarr.Length && reversed(arr, outarr)
  // post-conditions-end
{
// impl-start
  var i := 0;
  var j := arr.Length - 1;
  outarr := new char[arr.Length];
  outarr[0] := arr[j];
  i := i + 1;
  j := j - 1;
  while i < arr.Length && 0 <= j < arr.Length
    // invariants-start

    invariant 0 <= i <= arr.Length
    invariant j == arr.Length - 1 - i
    invariant forall k | 0 <= k < i :: outarr[k] == arr[arr.Length - 1 - k]
    decreases arr.Length - i, j
    // invariants-end

  {
    outarr[i] := arr[j];
    i := i + 1;
    j := j - 1;
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
  var s := ['a', 'b', 'a', 'b', 'a', 'b', 'a', 'b', 'a', 'b', 'a', 'b'];
  var a, b, c, d := new char[5], new char[5], new char[5], new char[5];
  a[0], a[1], a[2], a[3], a[4] := 'y', 'a', 'r', 'r', 'a';
  d[0], d[1], d[2], d[3], d[4] := 'y', 'a', 'r', 'r', 'a';
  b := yarra(a);
  c := yarra(b);
  // assert-start
  assert c[..] == a[..];
  // assert-end

// impl-end
}
