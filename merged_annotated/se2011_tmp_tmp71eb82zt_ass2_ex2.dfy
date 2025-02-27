method SecondLargest(a: array<int>) returns (seclar: int)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  if a.Length == 1 {
    seclar := a[0];
  } else {
    var l, s, i: int := 0, 0, 0;
    if a[1] > a[0] {
      l := a[1];
      s := a[0];
    } else {
      l := a[0];
      s := a[1];
    }
    while i < a.Length
      // invariants-start

      invariant 0 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> l >= a[j]
      invariant s <= l
      // invariants-end

    {
      if a[i] > l {
        s := l;
        l := a[i];
      }
      if a[i] > s && a[i] < l {
        s := a[i];
      }
      if s == l && s > a[i] {
        s := a[i];
      }
      i := i + 1;
    }
    seclar := s;
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
  var a: array<int> := new int[] [1];
  // assert-start
  assert a[0] == 1;
  // assert-end

  var x: int := SecondLargest(a);
  var b: array<int> := new int[] [9, 1];
  // assert-start
  assert b[0] == 9 && b[1] == 1;
  // assert-end

  x := SecondLargest(b);
  var c: array<int> := new int[] [1, 9];
  // assert-start
  assert c[0] == 1 && c[1] == 9;
  // assert-end

  x := SecondLargest(c);
  var d: array<int> := new int[] [2, 42, -4, 123, 42];
  // assert-start
  assert d[0] == 2 && d[1] == 42 && d[2] == -4 && d[3] == 123 && d[4] == 42;
  // assert-end

  x := SecondLargest(d);
  var e: array<int> := new int[] [1, 9, 8];
  // assert-start
  assert e[0] == 1 && e[1] == 9 && e[2] == 8;
  // assert-end

  x := SecondLargest(e);
// impl-end
}
