method MaxArray(a: array<int>) returns (max: int)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= max
  ensures exists i :: 0 <= i < a.Length && a[i] == max
  // post-conditions-end
{
// impl-start
  var i: nat := 1;
  max := a[0];
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] <= max
    invariant exists j :: 0 <= j < i && a[j] == max
    // invariants-end

  {
    if a[i] > max {
      max := a[i];
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
  var arr: array<int> := new int[] [-11, 2, 42, -4];
  var res := MaxArray(arr);
  // assert-start
  assert arr[0] == -11 && arr[1] == 2 && arr[2] == 42 && arr[3] == -4;
  // assert-end

  // assert-start
  assert res == 42;
  // assert-end

// impl-end
}
