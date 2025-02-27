function acheck(a: array<int>, n: int): bool
  requires n >= 1
  reads a
{
  a.Length % 2 == 0 &&
  forall i :: 
    0 <= i < a.Length ==>
      if i % n == 0 then a[i] == 0 else a[i] != 0
}
// pure-end

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var arr: array<int> := new int[] [0, 42, 0, 42];
  var res := acheck(arr, 2);
  // assert-start
  assert res;
  // assert-end

  arr := new int[] [];
  res := acheck(arr, 2);
  // assert-start
  assert res;
  // assert-end

  arr := new int[] [0, 4, 2, 0];
  // assert-start
  assert arr[2] == 2;
  // assert-end

  res := acheck(arr, 2);
  // assert-start
  assert !res;
  // assert-end

// impl-end
}
