method DoubleArray(src: array<int>, dst: array<int>)
  // pre-conditions-start
  requires src.Length == dst.Length
  // pre-conditions-end
  // post-conditions-start
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
  // post-conditions-end
{
// impl-start
  var n := 0;
  while n != src.Length
    // invariants-start

    invariant 0 <= n <= src.Length
    invariant forall i :: 0 <= i < n ==> dst[i] == 2 * old(src[i])
    invariant forall i :: n <= i < src.Length ==> src[i] == old(src[i])
    // invariants-end

  {
    dst[n] := 2 * src[n];
    n := n + 1;
  }
// impl-end
}
