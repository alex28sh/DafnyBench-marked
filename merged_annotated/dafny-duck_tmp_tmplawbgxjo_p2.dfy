function abs(x: int): nat
{
  if x < 0 then
    -x
  else
    x
}
// pure-end

method absx(x: array<int>) returns (y: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures y.Length == x.Length
  ensures forall i :: 0 <= i < y.Length ==> y[i] == abs(x[i])
  // post-conditions-end
{
// impl-start
  y := new int[x.Length];
  var j := 0;
  // assert-start
  assert y.Length == x.Length;
  // assert-end

  while j < y.Length
    // invariants-start

    invariant 0 <= j <= y.Length
    invariant forall i :: 0 <= i < j <= y.Length ==> y[i] == abs(x[i])
    // invariants-end

  {
    if x[j] < 0 {
      y[j] := -x[j];
    } else {
      y[j] := x[j];
    }
    j := j + 1;
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
  var d := new int[5];
  var c := new int[5];
  d[0], d[1], d[2], d[3], d[4] := -4, 1, 5, -2, -5;
  c := absx(d);
  // assert-start
  assert c[..] == [4, 1, 5, 2, 5];
  // assert-end

  print c[..];
// impl-end
}
