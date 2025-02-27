method Symmetric(a: array<int>) returns (flag: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures flag == true ==> forall x :: 0 <= x < a.Length ==> a[x] == a[a.Length - x - 1]
  ensures flag == false ==> exists x :: 0 <= x < a.Length && a[x] != a[a.Length - x - 1]
  // post-conditions-end
{
// impl-start
  if a.Length == 0 {
    return true;
  }
  var i: int := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall x :: 0 <= x < i ==> a[x] == a[a.Length - x - 1]
    // invariants-end

  {
    if a[i] != a[a.Length - i - 1] {
      return false;
    }
    i := i + 1;
  }
  return true;
// impl-end
}
