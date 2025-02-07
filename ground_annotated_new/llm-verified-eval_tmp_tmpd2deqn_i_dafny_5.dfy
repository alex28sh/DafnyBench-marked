method intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
  ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> interspersed[i] == numbers[i / 2]
  ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==> interspersed[i] == delimiter
  // post-conditions-end
{
// impl-start
  interspersed := [];
  for i := 0 to |numbers|
    // invariants-start

    invariant |interspersed| == if i > 0 then 2 * i - 1 else 0
    invariant forall i0 :: 0 <= i0 < |interspersed| ==> i0 % 2 == 0 ==> interspersed[i0] == numbers[i0 / 2]
    invariant forall i0 :: 0 <= i0 < |interspersed| ==> i0 % 2 == 1 ==> interspersed[i0] == delimiter
    // invariants-end

  {
    if i > 0 {
      interspersed := interspersed + [delimiter];
    }
    interspersed := interspersed + [numbers[i]];
  }
// impl-end
}
