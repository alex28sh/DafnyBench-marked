method single(x: array<int>, y: array<int>) returns (b: array<int>)
  // pre-conditions-start
  requires x.Length > 0
  requires y.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures b[..] == x[..] + y[..]
  // post-conditions-end
{
// impl-start
  b := new int[x.Length + y.Length];
  var i := 0;
  var index := 0;
  var sumi := x.Length + y.Length;
  while i < x.Length && index < sumi
    // invariants-start

    invariant 0 <= i <= x.Length
    invariant 0 <= index <= sumi
    invariant b[..index] == x[..i]
    // invariants-end

  {
    b[index] := x[i];
    i := i + 1;
    index := index + 1;
  }
  i := 0;
  while i < y.Length && index < sumi
    // invariants-start

    invariant 0 <= i <= y.Length
    invariant 0 <= index <= sumi
    invariant b[..index] == x[..] + y[..i]
    // invariants-end

  {
    b[index] := y[i];
    i := i + 1;
    index := index + 1;
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
  var a := new int[4] [1, 5, 2, 3];
  var b := new int[3] [4, 3, 5];
  var c := new int[7];
  c := single(a, b);
  // assert-start
  assert c[..] == [1, 5, 2, 3, 4, 3, 5];
  // assert-end

// impl-end
}
