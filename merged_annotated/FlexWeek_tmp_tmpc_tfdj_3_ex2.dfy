function abs(a: int): nat
{
  if a < 0 then
    -a
  else
    a
}
// pure-end

method aba(a: array<int>) returns (b: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a.Length == b.Length
  ensures forall x :: 0 <= x < b.Length ==> b[x] == abs(a[x])
  // post-conditions-end
{
// impl-start
  b := new int[a.Length];
  var i := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall x :: 0 <= x < i ==> b[x] == abs(a[x])
    // invariants-end

  {
    if a[i] < 0 {
      b[i] := -a[i];
    } else {
      b[i] := a[i];
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
  var a := new int[] [1, -2, -2, 1];
  var b := aba(a);
  // assert-start
  assert b[..] == [1, 2, 2, 1];
  // assert-end

// impl-end
}
