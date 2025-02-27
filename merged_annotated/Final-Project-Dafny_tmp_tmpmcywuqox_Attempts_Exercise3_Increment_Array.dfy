method incrementArray(a: array<int>)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  // post-conditions-end
{
// impl-start
  var j: int := 0;
  while j < a.Length
    // invariants-start

    invariant 0 <= j <= a.Length
    invariant forall i :: j <= i < a.Length ==> a[i] == old(a[i])
    invariant forall i :: 0 <= i < j ==> a[i] == old(a[i]) + 1
    decreases a.Length - j
    // invariants-end

  {
    // assert-start
    assert forall i :: 0 <= i < j ==> a[i] == old(a[i]) + 1;
    // assert-end

    // assert-start
    assert a[j] == old(a[j]);
    // assert-end

    a[j] := a[j] + 1;
    // assert-start
    assert forall i :: 0 <= i < j ==> a[i] == old(a[i]) + 1;
    // assert-end

    // assert-start
    assert a[j] == old(a[j]) + 1;
    // assert-end

    j := j + 1;
  }
// impl-end
}
