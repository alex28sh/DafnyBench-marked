method LinearSearch<T>(a: array<T>, P: T -> bool) returns (n: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures -1 <= n < a.Length
  ensures n == -1 || P(a[n])
  ensures n != -1 ==> forall i :: 0 <= i < n ==> !P(a[i])
  ensures n == -1 ==> forall i :: 0 <= i < a.Length ==> !P(a[i])
  // post-conditions-end
{
// impl-start
  n := 0;
  while n != a.Length
    // invariants-start

    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> !P(a[i])
    invariant n == -1 ==> forall i :: 0 <= i < n ==> !P(a[i])
    decreases a.Length - n
    // invariants-end

  {
    if P(a[n]) {
      return;
    }
    n := n + 1;
  }
  n := -1;
// impl-end
}

method LinearSearch1<T>(a: array<T>, P: T -> bool, s1: seq<T>)
    returns (n: int)
  // pre-conditions-start
  requires |s1| <= a.Length
  requires forall i :: 0 <= i < |s1| ==> s1[i] == a[i]
  // pre-conditions-end
  // post-conditions-start
  ensures -1 <= n < a.Length
  ensures n == -1 || P(a[n])
  ensures n != -1 ==> forall i :: 0 <= i < n ==> !P(a[i])
  ensures n == -1 ==> forall i :: 0 <= i < |s1| ==> !P(a[i])
  // post-conditions-end
{
// impl-start
  n := 0;
  while n != |s1|
    // invariants-start

    invariant 0 <= n <= |s1|
    invariant forall i :: 0 <= i < n ==> !P(a[i])
    invariant n == -1 ==> forall i :: 0 <= i < n ==> !P(a[i])
    decreases |s1| - n
    // invariants-end

  {
    if P(a[n]) {
      return;
    }
    n := n + 1;
  }
  n := -1;
// impl-end
}

method LinearSearch2<T(==)>(data: array<T>, Element: T, s1: seq<T>)
    returns (position: int)
  // pre-conditions-start
  requires |s1| <= data.Length
  requires forall i :: 0 <= i < |s1| ==> s1[i] == data[i]
  // pre-conditions-end
  // post-conditions-start
  ensures position == -1 || position >= 1
  ensures position >= 1 ==> exists i :: 0 <= i < |s1| && s1[i] == Element
  ensures position == -1 ==> forall i :: 0 <= i < |s1| ==> s1[i] != Element
  // post-conditions-end
{
// impl-start
  var n := 0;
  position := 0;
  while n != |s1|
    // invariants-start

    invariant 0 <= n <= |s1|
    invariant position >= 1 ==> exists i :: 0 <= i < |s1| && data[i] == Element
    invariant forall i :: |s1| - 1 - n < i < |s1| ==> data[i] != Element
    decreases |s1| - n
    // invariants-end

  {
    if data[|s1| - 1 - n] == Element {
      position := n + 1;
      return position;
    }
    n := n + 1;
  }
  position := -1;
// impl-end
}

method LinearSearch3<T(==)>(data: array<T>, Element: T, s1: seq<T>)
    returns (position: int)
  // pre-conditions-start
  requires |s1| <= data.Length
  requires forall i :: 0 <= i < |s1| ==> s1[i] == data[data.Length - 1 - i]
  // pre-conditions-end
  // post-conditions-start
  ensures position == -1 || position >= 1
  ensures position >= 1 ==> exists i :: 0 <= i < |s1| && s1[i] == Element && |s1| != 0
  // post-conditions-end
{
// impl-start
  var n := 0;
  var n1 := |s1|;
  position := 0;
  while n != |s1|
    // invariants-start

    invariant 0 <= n <= |s1|
    invariant position >= 1 ==> exists i :: 0 <= i < |s1| && s1[i] == Element
    invariant forall i :: data.Length - n1 < i < data.Length - n1 + n ==> data[i] != Element
    invariant forall i :: |s1| - 1 - n < i < |s1| - 1 ==> s1[i] != Element
    decreases |s1| - n
    // invariants-end

  {
    if data[data.Length - n1 + n] == Element {
      position := n + 1;
      // assert-start
      assert data[data.Length - n1] == s1[|s1| - 1];
      // assert-end

      // assert-start
      assert data[data.Length - n1 + n] == s1[n1 - 1 - n];
      // assert-end

      // assert-start
      assert forall i :: 0 <= i < |s1| ==> s1[i] == data[data.Length - 1 - i];
      // assert-end

      // assert-start
      assert forall i :: data.Length - n1 < i < data.Length - n1 + n ==> data[i] != Element;
      // assert-end

      // assert-start
      assert forall i :: |s1| - 1 > i > |s1| - 1 - n ==> s1[i] != Element;
      // assert-end

      // assert-start
      assert forall i :: data.Length - |s1| < i < data.Length - 1 ==> data[i] == s1[data.Length - i - 1];
      // assert-end

      return position;
    }
    n := n + 1;
  }
  position := -1;
  // assert-start
  assert |s1| <= data.Length;
  // assert-end

  // assert-start
  assert |s1| != 0 ==> s1[0] == data[data.Length - 1];
  // assert-end

  // assert-start
  assert |s1| != 0 ==> data[data.Length - n1] == s1[|s1| - 1];
  // assert-end

  // assert-start
  assert forall i :: data.Length - |s1| < i < data.Length - 1 ==> data[i] == s1[data.Length - i - 1];
  // assert-end

  // assert-start
  assert forall i :: data.Length - n1 < i < data.Length - n1 + n ==> data[i] != Element;
  // assert-end

  // assert-start
  assert forall i :: 0 <= i < |s1| ==> s1[i] == data[data.Length - 1 - i];
  // assert-end

  // assert-start
  assert forall i :: |s1| - 1 > i > |s1| - 1 - n ==> s1[i] != Element;
  // assert-end

// impl-end
}
