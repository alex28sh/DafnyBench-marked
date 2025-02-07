function sumcheck(s: array<int>, i: int): int
  requires 0 <= i <= s.Length
  reads s
{
  if i == 0 then
    0
  else
    s[i - 1] + sumcheck(s, i - 1)
}
// pure-end

method sum(s: array<int>) returns (a: int)
  // pre-conditions-start
  requires s.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures sumcheck(s, s.Length) == a
  // post-conditions-end
{
// impl-start
  a := 0;
  var i: int := 0;
  while i < s.Length
    // invariants-start

    invariant 0 <= i <= s.Length && a == sumcheck(s, i)
    // invariants-end

  {
    a := a + s[i];
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
  var a: array<int> := new int[4];
  a[0] := 1;
  a[1] := 3;
  a[2] := 3;
  a[3] := 2;
  // assert-start
  assert a[..] == [1, 3, 3, 2];
  // assert-end

  var s := sum(a);
  // assert-start
  assert a[0] == 1 && a[1] == 3 && a[2] == 3 && a[3] == 2;
  // assert-end

  // assert-start
  assert s == sumcheck(a, a.Length);
  // assert-end

  print "\nThe sum of all elements in [1,3,3,2] is ";
  print s;
// impl-end
}
