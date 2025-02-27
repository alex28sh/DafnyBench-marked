method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
// impl-end
}

method H(a: array<int>, c: array<int>, n: nat, j: nat)
  // pre-conditions-start
  requires j < n == a.Length == c.Length
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var A := a[..];
  var C := c[..];
  if {
    case A[j] == C[j] =>
      // assert-start
      assert a[j] == c[j];
      // assert-end

    case forall i :: 0 <= i < n ==> A[i] == C[i] =>
      // assert-start
      assert a[j] == c[j];
      // assert-end

    case forall i :: 0 <= i < n ==> A[i] == C[i] =>
      // assert-start
      assert forall i :: 0 <= i < n ==> a[i] == c[i];
      // assert-end

    case A == C =>
      // assert-start
      assert forall i :: 0 <= i < n ==> A[i] == C[i];
      // assert-end

    case A == C =>
      // assert-start
      assert forall i :: 0 <= i < n ==> a[i] == c[i];
      // assert-end

    case true =>
  }
// impl-end
}

method K(a: array<int>, c: array<int>, n: nat)
  // pre-conditions-start
  requires n <= a.Length && n <= c.Length
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var A := a[..n];
  var C := c[..n];
  if {
    case A == C =>
      // assert-start
      assert forall i :: 0 <= i < n ==> A[i] == C[i];
      // assert-end

    case A == C =>
      // assert-start
      assert forall i :: 0 <= i < n ==> a[i] == c[i];
      // assert-end

    case true =>
  }
// impl-end
}

method L(a: array<int>, c: array<int>, n: nat)
  // pre-conditions-start
  requires n <= a.Length == c.Length
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var A := a[n..];
  var C := c[n..];
  var h := a.Length - n;
  if {
    case A == C =>
      // assert-start
      assert forall i :: 0 <= i < h ==> A[i] == C[i];
      // assert-end

    case A == C =>
      // assert-start
      assert forall i :: n <= i < n + h ==> a[i] == c[i];
      // assert-end

    case true =>
  }
// impl-end
}

method M(a: array<int>, c: array<int>, m: nat, n: nat, k: nat, l: nat)
  // pre-conditions-start
  requires k + m <= a.Length
  requires l + n <= c.Length
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var A := a[k .. k + m];
  var C := c[l .. l + n];
  if A == C {
    if * {
      // assert-start
      assert m == n;
      // assert-end

    } else if * {
      // assert-start
      assert forall i :: 0 <= i < n ==> A[i] == C[i];
      // assert-end

    } else if * {
      // assert-start
      assert forall i {:nowarn} :: k <= i < k + n ==> A[i - k] == C[i - k];
      // assert-end

    } else if * {
      // assert-start
      assert forall i :: 0 <= i < n ==> A[i] == a[k + i];
      // assert-end

    } else if * {
      // assert-start
      assert forall i :: 0 <= i < n ==> C[i] == c[l + i];
      // assert-end

    } else if * {
      // assert-start
      assert forall i {:nowarn} :: 0 <= i < n ==> a[k + i] == c[l + i];
      // assert-end

    }
  }
// impl-end
}

method M'(a: array<int>, c: array<int>, m: nat, n: nat, k: nat, l: nat)
  // pre-conditions-start
  requires k + m <= a.Length
  requires l + n <= c.Length
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  if {
    case l + m <= c.Length && forall i :: 0 <= i < m ==> a[i] == c[l + i] =>
      // assert-start
      assert a[..m] == c[l .. l + m];
      // assert-end

    case l + a.Length <= c.Length && forall i :: k <= i < a.Length ==> a[i] == c[l + i] =>
      // assert-start
      assert a[k..] == c[l + k .. l + a.Length];
      // assert-end

    case l + k + m <= c.Length && forall i :: k <= i < k + m ==> a[i] == c[l + i] =>
      // assert-start
      assert a[k .. k + m] == c[l + k .. l + k + m];
      // assert-end

    case true =>
  }
// impl-end
}
