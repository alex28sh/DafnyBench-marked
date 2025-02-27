method remove_front(a: array<int>) returns (c: array<int>)
  // pre-conditions-start
  requires a.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures a[1..] == c[..]
  // post-conditions-end
{
// impl-start
  c := new int[a.Length - 1];
  var i := 1;
  while i < a.Length
    // invariants-start

    invariant 1 <= i <= a.Length
    invariant forall ii :: 1 <= ii < i ==> c[ii - 1] == a[ii]
    // invariants-end

  {
    c[i - 1] := a[i];
    i := i + 1;
  }
// impl-end
}
