method ArraySplit(a: array<int>) returns (b: array<int>, c: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures fresh(b)
  ensures fresh(c)
  ensures a[..] == b[..] + c[..]
  ensures a.Length == b.Length + c.Length
  ensures a.Length > 1 ==> a.Length > b.Length
  ensures a.Length > 1 ==> a.Length > c.Length
  // post-conditions-end
{
// impl-start
  var splitPoint: int := a.Length / 2;
  b := new int[splitPoint];
  c := new int[a.Length - splitPoint];
  var i: int := 0;
  while i < splitPoint
    // invariants-start

    invariant 0 <= i <= splitPoint
    invariant b[..i] == a[..i]
    // invariants-end

  {
    b[i] := a[i];
    i := i + 1;
  }
  var j: int := 0;
  while i < a.Length
    // invariants-start

    invariant splitPoint <= i <= a.Length
    invariant j == i - splitPoint
    invariant c[..j] == a[splitPoint .. i]
    invariant b[..] + c[..j] == a[..i]
    // invariants-end

  {
    c[j] := a[i];
    i := i + 1;
    j := j + 1;
  }
// impl-end
}
