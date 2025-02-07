method has_close_elements(numbers: seq<real>, threshold: real) returns (res: bool)
  // pre-conditions-start
  requires threshold >= 0.0
  // pre-conditions-end
  // post-conditions-start
  ensures res ==> exists i: int, j: int :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) < threshold
  ensures !res ==> forall i: int, j: int :: 1 <= i < |numbers| && 0 <= j < i ==> (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) >= threshold
  // post-conditions-end
{
// impl-start
  res := false;
  var idx: int := 0;
  while idx < |numbers| && !res
    // invariants-start

    invariant 0 <= idx <= |numbers|
    invariant !res
    invariant forall i: int, j: int :: 0 <= i < idx && 0 <= j < i ==> (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) >= threshold
    // invariants-end

  {
    var idx2: int := 0;
    while idx2 < idx && !res
      // invariants-start

      invariant 0 <= idx <= |numbers|
      invariant 0 <= idx2 <= idx
      invariant !res
      invariant forall j: int :: 0 <= j < idx2 ==> (if numbers[idx] - numbers[j] < 0.0 then numbers[j] - numbers[idx] else numbers[idx] - numbers[j]) >= threshold
      // invariants-end

    {
      var distance := if numbers[idx2] - numbers[idx] < 0.0 then numbers[idx] - numbers[idx2] else numbers[idx2] - numbers[idx];
      if distance < threshold {
        res := true;
        return;
      }
      idx2 := idx2 + 1;
    }
    idx := idx + 1;
  }
// impl-end
}
