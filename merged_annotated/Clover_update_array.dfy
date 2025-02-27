method UpdateElements(a: array<int>)
  // pre-conditions-start
  requires a.Length >= 8
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures old(a[4]) + 3 == a[4]
  ensures a[7] == 516
  ensures forall i :: 0 <= i < a.Length ==> i != 7 && i != 4 ==> a[i] == old(a[i])
  // post-conditions-end
{
// impl-start
  a[4] := a[4] + 3;
  a[7] := 516;
// impl-end
}
