function abs(x: real): real
{
  if x < 0.0 then
    -x
  else
    x
}
// pure-end

method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> exists i, j :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && abs(numbers[i] - numbers[j]) < threshold
  ensures result ==> |numbers| > 1
  // post-conditions-end
{
// impl-start
  result := false;
  // assert-start
  assert forall i0 :: 0 <= i0 < 0 ==> forall j0 :: 0 <= j0 < |numbers| ==> abs(numbers[i0] - numbers[j0]) >= threshold;
  // assert-end

  for i := 0 to |numbers|
    // invariants-start

    invariant forall i0 :: 0 <= i0 < i ==> forall j0 :: 0 <= j0 < |numbers| ==> i0 != j0 ==> abs(numbers[i0] - numbers[j0]) >= threshold
    // invariants-end

  {
    for j := 0 to |numbers|
      // invariants-start

      invariant forall i0 :: 0 <= i0 <= i ==> forall j0 :: 0 <= j0 < j ==> i0 != j0 ==> abs(numbers[i0] - numbers[j0]) >= threshold
      // invariants-end

    {
      if i != j && abs(numbers[i] - numbers[j]) < threshold {
        // assert-start
        assert abs(numbers[i] - numbers[j]) < threshold;
        // assert-end

        result := true;
        return;
      }
    }
  }
// impl-end
}
