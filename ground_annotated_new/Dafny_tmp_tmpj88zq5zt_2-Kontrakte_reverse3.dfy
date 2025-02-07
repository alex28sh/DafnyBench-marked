method swap3(a: array<int>, h: int, i: int, j: int)
  // pre-conditions-start
  requires 0 <= h < a.Length
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  requires i != j && j != h && h != i
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures a[h] == old(a[i])
  ensures a[j] == old(a[h])
  ensures a[i] == old(a[j])
  ensures forall k: int :: 0 <= k < a.Length && k != h && k != i && k != j ==> a[k] == old(a[k])
  // post-conditions-end
{
// impl-start
  var tmp := a[h];
  a[h] := a[i];
  a[i] := a[j];
  a[j] := tmp;
// impl-end
}

method testSwap3(a: array<int>, h: int, i: int, j: int)
  // pre-conditions-start
  requires 0 <= h < a.Length
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  requires i != j && j != h && h != i
  // pre-conditions-end
  // post-conditions-start
  modifies a
  // post-conditions-end
{
// impl-start
  swap3(a, h, i, j);
  // assert-start
  assert a[h] == old(a[i]);
  // assert-end

  // assert-start
  assert a[j] == old(a[h]);
  // assert-end

  // assert-start
  assert a[i] == old(a[j]);
  // assert-end

  // assert-start
  assert forall k: int :: 0 <= k < a.Length && k != h && k != i && k != j ==> a[k] == old(a[k]);
  // assert-end

// impl-end
}
