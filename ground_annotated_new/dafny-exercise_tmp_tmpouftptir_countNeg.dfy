function verifyNeg(a: array<int>, idx: int): nat
  requires 0 <= idx <= a.Length
  reads a
{
  if idx == 0 then
    0
  else
    verifyNeg(a, idx - 1) + if a[idx - 1] < 0 then 1 else 0
}
// pure-end

method CountNeg(a: array<int>) returns (cnt: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures cnt == verifyNeg(a, a.Length)
  // post-conditions-end
{
// impl-start
  var i := 0;
  cnt := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant cnt == verifyNeg(a, i)
    // invariants-end

  {
    if a[i] < 0 {
      cnt := cnt + 1;
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
  var arr: array<int> := new int[] [0, -1, -2, 4];
  var res := CountNeg(arr);
  // assert-start
  assert res == verifyNeg(arr, arr.Length);
  // assert-end

// impl-end
}
