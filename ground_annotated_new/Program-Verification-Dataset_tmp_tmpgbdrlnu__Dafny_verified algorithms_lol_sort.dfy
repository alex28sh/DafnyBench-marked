function valid_permut(a: seq<int>, b: seq<int>): bool
  requires |a| == |b|
{
  multiset(a) == multiset(b)
}
// pure-end

method swap(a: array<int>, i: int, j: int)
  // pre-conditions-start
  requires 0 <= i < a.Length && 0 <= j < a.Length
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures a[..] == old(a[..])[i := old(a[j])][j := old(a[i])]
  ensures valid_permut(a[..], old(a[..]))
  // post-conditions-end
{
// impl-start
  a[i], a[j] := a[j], a[i];
// impl-end
}

function sorted(a: seq<int>): bool
{
  forall i, j | 0 <= i <= j < |a| :: 
    a[i] <= a[j]
}
// pure-end

method lol_sort(a: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures valid_permut(a[..], old(a[..]))
  ensures sorted(a[..])
  // post-conditions-end
{
// impl-start
  for i := 0 to a.Length
    // invariants-start

    invariant valid_permut(a[..], old(a[..]))
    invariant sorted(a[..i])
    // invariants-end

  {
    for j := 0 to a.Length
      // invariants-start

      invariant valid_permut(a[..], old(a[..]))
      invariant j < i ==> forall k | 0 <= k < j :: a[k] <= a[i]
      invariant j < i ==> sorted(a[..i])
      invariant j >= i ==> sorted(a[..i + 1])
      // invariants-end

    {
      if a[i] < a[j] {
        swap(a, i, j);
      }
    }
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
  var a := new int[] [3, 1, 4, 1, 5, 9, 2, 6];
  lol_sort(a);
  print a[..];
  // assert-start
  expect a[..] == [1, 1, 2, 3, 4, 5, 6, 9];
  // assert-end

  var empty := new int[] [];
  lol_sort(empty);
  // assert-start
  assert empty[..] == [];
  // assert-end

// impl-end
}
