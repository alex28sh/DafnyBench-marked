method SetEndPoints(a: array<int>, left: int, right: int)
  // pre-conditions-start
  requires a.Length != 0
  // pre-conditions-end
  // post-conditions-start
  modifies a
  // post-conditions-end
{
// impl-start
  a[0] := left;
  a[a.Length - 1] := right;
// impl-end
}

method Aliases(a: array<int>, b: array<int>)
  // pre-conditions-start
  requires a.Length >= b.Length > 100
  // pre-conditions-end
  // post-conditions-start
  modifies a
  // post-conditions-end
{
// impl-start
  a[0] := 10;
  var c := a;
  if b == a {
    b[10] := b[0] + 1;
  }
  c[20] := a[14] + 2;
// impl-end
}

method NewArray() returns (a: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a.Length == 20
  ensures fresh(a)
  // post-conditions-end
{
// impl-start
  a := new int[20];
  var b := new int[30];
  a[6] := 216;
  b[7] := 343;
// impl-end
}

method Caller()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := NewArray();
  a[8] := 512;
// impl-end
}

method InitArray<T>(a: array<T>, d: T)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == d
  // post-conditions-end
{
// impl-start
  var n := 0;
  while n != a.Length
    // invariants-start

    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> a[i] == d
    // invariants-end

  {
    a[n] := d;
    n := n + 1;
  }
// impl-end
}

method UpdateElements(a: array<int>)
  // pre-conditions-start
  requires a.Length == 10
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures old(a[4]) < a[4]
  ensures a[6] <= old(a[6])
  ensures a[8] == old(a[8])
  // post-conditions-end
{
// impl-start
  a[4] := a[4] + 3;
  a[8] := a[8] + 1;
  a[7] := 516;
  a[8] := a[8] - 1;
// impl-end
}

method IncrementArray(a: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  // post-conditions-end
{
// impl-start
  var n := 0;
  while n != a.Length
    // invariants-start

    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> a[i] == old(a[i]) + 1
    invariant forall i :: n <= i < a.Length ==> a[i] == old(a[i])
    // invariants-end

  {
    a[n] := a[n] + 1;
    n := n + 1;
  }
// impl-end
}

method CopyArray<T>(a: array<T>, b: array<T>)
  // pre-conditions-start
  requires a.Length == b.Length
  // pre-conditions-end
  // post-conditions-start
  modifies b
  ensures forall i :: 0 <= i < a.Length ==> b[i] == old(a[i])
  // post-conditions-end
{
// impl-start
  var n := 0;
  while n != a.Length
    // invariants-start

    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> b[i] == old(a[i])
    invariant forall i :: 0 <= i < a.Length ==> a[i] == old(a[i])
    // invariants-end

  {
    b[n] := a[n];
    n := n + 1;
  }
// impl-end
}
