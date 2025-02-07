function Sum(arr: array<int>, len: int): int
  requires arr.Length > 0 && 0 <= len <= arr.Length
  reads arr
{
  if len == 0 then
    0
  else
    arr[len - 1] + Sum(arr, len - 1)
}
// pure-end

method SumArray(arr: array<int>) returns (sum: int)
  // pre-conditions-start
  requires arr.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures sum == Sum(arr, arr.Length)
  // post-conditions-end
{
// impl-start
  sum := 0;
  var i := 0;
  while i < arr.Length
    // invariants-start

    invariant 0 <= i <= arr.Length
    invariant sum == Sum(arr, i)
    // invariants-end

  {
    sum := sum + arr[i];
    i := i + 1;
  }
// impl-end
}
