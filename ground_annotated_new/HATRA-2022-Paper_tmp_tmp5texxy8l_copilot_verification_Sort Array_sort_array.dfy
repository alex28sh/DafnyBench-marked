method sortArray(arr: array<int>) returns (arr_sorted: array<int>)
  // pre-conditions-start
  requires 0 <= arr.Length < 10000
  // pre-conditions-end
  // post-conditions-start
  modifies arr
  ensures sorted(arr_sorted, 0, arr_sorted.Length)
  ensures multiset(arr[..]) == multiset(arr_sorted[..])
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < arr.Length
    // invariants-start

    invariant i <= arr.Length
    invariant sorted(arr, 0, i)
    invariant multiset(old(arr[..])) == multiset(arr[..])
    invariant forall u, v :: 0 <= u < i && i <= v < arr.Length ==> arr[u] <= arr[v]
    invariant pivot(arr, i)
    // invariants-end

  {
    var j := i;
    while j < arr.Length
      // invariants-start

      invariant j <= arr.Length
      invariant multiset(old(arr[..])) == multiset(arr[..])
      invariant pivot(arr, i)
      invariant forall u :: i < u < j ==> arr[i] <= arr[u]
      invariant forall u :: 0 <= u < i ==> arr[u] <= arr[i]
      invariant sorted(arr, 0, i + 1)
      // invariants-end

    {
      if arr[i] > arr[j] {
        var temp := arr[i];
        arr[i] := arr[j];
        arr[j] := temp;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return arr;
// impl-end
}

function sorted(arr: array<int>, start: int, end: int): bool
  requires 0 <= start <= end <= arr.Length
  reads arr
{
  forall i, j :: 
    start <= i <= j < end ==>
      arr[i] <= arr[j]
}
// pure-end

function pivot(arr: array<int>, pivot: int): bool
  requires 0 <= pivot <= arr.Length
  reads arr
{
  forall u, v :: 
    0 <= u < pivot < v < arr.Length ==>
      arr[u] <= arr[v]
}
// pure-end
