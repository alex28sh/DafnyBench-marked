method partitionOddEven(a: array<nat>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures !exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])
  // post-conditions-end
{
// impl-start
  var i := 0;
  var j := a.Length - 1;
  while i <= j
    // invariants-start

    invariant 0 <= i <= j + 1 <= a.Length
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant forall k :: 0 <= k < i ==> odd(a[k])
    invariant forall k :: j < k < a.Length ==> even(a[k])
    // invariants-end

  {
    if even(a[i]) && odd(a[j]) {
      a[i], a[j] := a[j], a[i];
    }
    if odd(a[i]) {
      i := i + 1;
    }
    if even(a[j]) {
      j := j - 1;
    }
  }
// impl-end
}

function odd(n: nat): bool
{
  n % 2 == 1
}
// pure-end

function even(n: nat): bool
{
  n % 2 == 0
}
// pure-end

method testPartitionOddEven()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a: array<nat> := new [] [1, 2, 3];
  // assert-start
  assert a[..] == [1, 2, 3];
  // assert-end

  partitionOddEven(a);
  // assert-start
  assert a[..] == [1, 3, 2] || a[..] == [3, 1, 2];
  // assert-end

// impl-end
}
