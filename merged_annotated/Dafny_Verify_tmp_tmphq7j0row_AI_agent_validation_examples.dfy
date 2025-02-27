function Power(n: nat): nat
{
  if n == 0 then
    1
  else
    2 * Power(n - 1)
}
// pure-end

method ComputePower(N: int) returns (y: nat)
  // pre-conditions-start
  requires N >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures y == Power(N)
  // post-conditions-end
{
// impl-start
  y := 1;
  var x := 0;
  while x != N
    // invariants-start

    invariant 0 <= x <= N
    invariant y == Power(x)
    decreases N - x
    // invariants-end

  {
    x, y := x + 1, y + y;
  }
// impl-end
}

method Max(a: array<nat>) returns (m: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i]
  // post-conditions-end
{
// impl-start
  m := 0;
  var n := 0;
  while n != a.Length
    // invariants-start

    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> a[i] <= m
    invariant (m == 0 && n == 0) || exists i :: 0 <= i < n && m == a[i]
    // invariants-end

  {
    if m < a[n] {
      m := a[n];
    }
    n := n + 1;
  }
// impl-end
}

method Cube(n: nat) returns (c: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures c == n * n * n
  // post-conditions-end
{
// impl-start
  c := 0;
  var i := 0;
  var k := 1;
  var m := 6;
  while i != n
    // invariants-start

    invariant 0 <= i <= n
    invariant c == i * i * i
    invariant k == 3 * i * i + 3 * i + 1
    invariant m == 6 * i + 6
    // invariants-end

  {
    c, k, m := c + k, k + m, m + 6;
    i := i + 1;
  }
// impl-end
}

method IncrementMatrix(a: array2<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
  // post-conditions-end
{
// impl-start
  var m := 0;
  while m != a.Length0
    // invariants-start

    invariant 0 <= m <= a.Length0
    invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
    invariant forall i, j :: m <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j])
    // invariants-end

  {
    var n := 0;
    while n != a.Length1
      // invariants-start

      invariant 0 <= n <= a.Length1
      invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j]) + 1
      invariant forall i, j :: m < i < a.Length0 && 0 <= j < a.Length1 ==> a[i, j] == old(a[i, j])
      invariant forall j :: 0 <= j < n ==> a[m, j] == old(a[m, j]) + 1
      invariant forall j :: n <= j < a.Length1 ==> a[m, j] == old(a[m, j])
      // invariants-end

    {
      a[m, n] := a[m, n] + 1;
      n := n + 1;
    }
    m := m + 1;
  }
// impl-end
}

method CopyMatrix(src: array2, dst: array2)
  // pre-conditions-start
  requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
  // pre-conditions-end
  // post-conditions-start
  modifies dst
  ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i, j] == old(src[i, j])
  // post-conditions-end
{
// impl-start
  var m := 0;
  while m != src.Length0
    // invariants-start

    invariant 0 <= m <= src.Length0
    invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i, j] == old(src[i, j])
    invariant forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> src[i, j] == old(src[i, j])
    // invariants-end

  {
    var n := 0;
    while n != src.Length1
      // invariants-start

      invariant 0 <= n <= src.Length1
      invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i, j] == old(src[i, j])
      invariant forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> src[i, j] == old(src[i, j])
      invariant forall j :: 0 <= j < n ==> dst[m, j] == old(src[m, j])
      // invariants-end

    {
      dst[m, n] := src[m, n];
      n := n + 1;
    }
    m := m + 1;
  }
// impl-end
}

method DoubleArray(src: array<int>, dst: array<int>)
  // pre-conditions-start
  requires src.Length == dst.Length
  // pre-conditions-end
  // post-conditions-start
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
  // post-conditions-end
{
// impl-start
  var n := 0;
  while n != src.Length
    // invariants-start

    invariant 0 <= n <= src.Length
    invariant forall i :: 0 <= i < n ==> dst[i] == 2 * old(src[i])
    invariant forall i :: n <= i < src.Length ==> src[i] == old(src[i])
    // invariants-end

  {
    dst[n] := 2 * src[n];
    n := n + 1;
  }
// impl-end
}

method RotateLeft(a: array)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[i + 1])
  ensures a[a.Length - 1] == old(a[0])
  // post-conditions-end
{
// impl-start
  var n := 0;
  while n != a.Length - 1
    // invariants-start

    invariant 0 <= n <= a.Length - 1
    invariant forall i :: 0 <= i < n ==> a[i] == old(a[i + 1])
    invariant a[n] == old(a[0])
    invariant forall i :: n < i <= a.Length - 1 ==> a[i] == old(a[i])
    // invariants-end

  {
    a[n], a[n + 1] := a[n + 1], a[n];
    n := n + 1;
  }
// impl-end
}

method RotateRight(a: array)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall i :: 1 <= i < a.Length ==> a[i] == old(a[i - 1])
  ensures a[0] == old(a[a.Length - 1])
  // post-conditions-end
{
// impl-start
  var n := 1;
  while n != a.Length
    // invariants-start

    invariant 1 <= n <= a.Length
    invariant forall i :: 1 <= i < n ==> a[i] == old(a[i - 1])
    invariant a[0] == old(a[n - 1])
    invariant forall i :: n <= i <= a.Length - 1 ==> a[i] == old(a[i])
    // invariants-end

  {
    a[0], a[n] := a[n], a[0];
    n := n + 1;
  }
// impl-end
}
