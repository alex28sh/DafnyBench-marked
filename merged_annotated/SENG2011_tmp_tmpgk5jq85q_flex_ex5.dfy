method firste(a: array<char>) returns (c: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures -1 <= c < a.Length
  ensures 0 <= c < a.Length ==> a[c] == 'e' && forall x :: 0 <= x < c ==> a[x] != 'e'
  ensures c == -1 ==> forall x :: 0 <= x < a.Length ==> a[x] != 'e'
  // post-conditions-end
{
// impl-start
  var i: int := 0;
  while i < a.Length
    // invariants-start

    invariant 0 <= i <= a.Length
    invariant forall x :: 0 <= x < i ==> a[x] != 'e'
    // invariants-end

  {
    if a[i] == 'e' {
      return i;
    }
    i := i + 1;
  }
  return -1;
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new char[6] ['c', 'h', 'e', 'e', 's', 'e'];
  var p := firste(a);
  print p;
// impl-end
}
