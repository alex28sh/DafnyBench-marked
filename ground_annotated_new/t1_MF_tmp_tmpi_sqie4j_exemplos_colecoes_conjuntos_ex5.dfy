function to_seq<T>(a: array<T>, i: int): (res: seq<T>)
  requires 0 <= i <= a.Length
  reads a
  ensures res == a[i..]
  decreases a.Length - i
{
  if i == a.Length then
    []
  else
    [a[i]] + to_seq(a, i + 1)
}
// pure-end

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a: array<int> := new int[2];
  a[0] := 2;
  a[1] := 3;
  var ms: multiset<int> := multiset(a[..]);
  // assert-start
  assert a[..] == to_seq(a, 0);
  // assert-end

  // assert-start
  assert ms[2] == 1;
  // assert-end

// impl-end
}
