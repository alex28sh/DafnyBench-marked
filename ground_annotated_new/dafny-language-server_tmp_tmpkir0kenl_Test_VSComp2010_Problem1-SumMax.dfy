method M(N: int, a: array<int>)
    returns (sum: int, max: int)
  // pre-conditions-start
  requires 0 <= N && a.Length == N && forall k :: 0 <= k && k < N ==> 0 <= a[k]
  // pre-conditions-end
  // post-conditions-start
  ensures sum <= N * max
  // post-conditions-end
{
// impl-start
  sum := 0;
  max := 0;
  var i := 0;
  while i < N
    // invariants-start

    invariant i <= N && sum <= i * max
    // invariants-end

  {
    if max < a[i] {
      max := a[i];
    }
    sum := sum + a[i];
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
  var a := new int[10];
  a[0] := 9;
  a[1] := 5;
  a[2] := 0;
  a[3] := 2;
  a[4] := 7;
  a[5] := 3;
  a[6] := 2;
  a[7] := 1;
  a[8] := 10;
  a[9] := 6;
  var s, m := M(10, a);
  print "N = ", a.Length, "  sum = ", s, "  max = ", m, "\n";
// impl-end
}
