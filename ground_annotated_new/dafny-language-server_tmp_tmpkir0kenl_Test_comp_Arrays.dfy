method LinearSearch(a: array<int>, key: int) returns (n: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= n <= a.Length
  ensures n == a.Length || a[n] == key
  // post-conditions-end
{
// impl-start
  n := 0;
  while n < a.Length
    // invariants-start

    invariant n <= a.Length
    // invariants-end

  {
    if a[n] == key {
      return;
    }
    n := n + 1;
  }
// impl-end
}

method PrintArray<A>(a: array?<A>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  if a == null {
    print "It's null\n";
  } else {
    var i := 0;
    while i < a.Length
      // invariants-start

      // invariants-end
 {
      print a[i], " ";
      i := i + 1;
    }
    print "\n";
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
  var a := new int[23];
  var i := 0;
  while i < 23
    // invariants-start

    // invariants-end
 {
    a[i] := i;
    i := i + 1;
  }
  PrintArray(a);
  var n := LinearSearch(a, 17);
  print n, "\n";
  var s: seq<int> := a[..];
  print s, "\n";
  s := a[2 .. 16];
  print s, "\n";
  s := a[20..];
  print s, "\n";
  s := a[..8];
  print s, "\n";
  a[0] := 42;
  print s, "\n";
  InitTests();
  MultipleDimensions();
  PrintArray<int>(null);
// impl-end
}

method InitTests()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var aa := new lowercase[3];
  PrintArray(aa);
  var s := "hello";
  aa := new lowercase[|s|] (i requires 0 <= i < |s| => s[i]);
  PrintArray(aa);
// impl-end
}

method MultipleDimensions()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var matrix := new int[2, 8];
  PrintMatrix(matrix);
  matrix := DiagMatrix(3, 5, 0, 1);
  PrintMatrix(matrix);
  var cube := new int[3, 0, 4] ((_ /* _v0 */, _ /* _v1 */, _ /* _v2 */) => 16);
  print "cube dims: ", cube.Length0, " ", cube.Length1, " ", cube.Length2, "\n";
// impl-end
}

method DiagMatrix<A>(rows: int, cols: int, zero: A, one: A)
    returns (a: array2<A>)
  // pre-conditions-start
  requires rows >= 0 && cols >= 0
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  return new A[rows, cols] ((x, y) => if x == y then one else zero);
// impl-end
}

method PrintMatrix<A>(m: array2<A>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < m.Length0
    // invariants-start

    // invariants-end
 {
    var j := 0;
    while j < m.Length1
      // invariants-start

      // invariants-end
 {
      print m[i, j], " ";
      j := j + 1;
    }
    print "\n";
    i := i + 1;
  }
// impl-end
}

type lowercase = ch
  | 'a' <= ch <= 'z'
  witness 'd'
