method ZapNegatives(a: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> if old(a[i]) < 0 then a[i] == 0 else a[i] == old(a[i])
  ensures a.Length == old(a).Length
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> if old(a[j]) < 0 then a[j] == 0 else a[j] == old(a[j])
    invariant forall j :: i <= j < a.Length ==> a[j] == old(a[j])
    // invariants-end

  {
    if a[i] < 0 {
      a[i] := 0;
    }
    i := i + 1;
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
  var arr: array<int> := new int[] [-1, 2, 3, -4];
  // assert-start
  assert arr[0] == -1 && arr[1] == 2 && arr[2] == 3 && arr[3] == -4;
  // assert-end

  ZapNegatives(arr);
  // assert-start
  assert arr[0] == 0 && arr[1] == 2 && arr[2] == 3 && arr[3] == 0;
  // assert-end

// impl-end
}
