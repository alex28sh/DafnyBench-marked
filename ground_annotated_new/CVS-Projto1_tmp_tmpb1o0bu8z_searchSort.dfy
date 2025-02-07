method fillK(a: array<int>, n: int, k: int, c: int)
    returns (b: bool)
  // pre-conditions-start
  requires 0 <= c <= n
  requires n == a.Length
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  if c == 0 {
    return true;
  }
  var p := 0;
  while p < c
    // invariants-start

    invariant 0 <= p <= c
    // invariants-end

  {
    if a[p] != k {
      return false;
    }
    p := p + 1;
  }
  return true;
// impl-end
}

method containsSubString(a: array<char>, b: array<char>) returns (pos: int)
  // pre-conditions-start
  requires 0 <= b.Length <= a.Length
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  pos := -1;
  if b.Length == 0 {
    return pos;
  }
  var p := 0;
  while p < a.Length
    // invariants-start

    invariant 0 <= p <= a.Length
    // invariants-end

  {
    if a.Length - p < b.Length {
      return pos;
    }
    if a[p] == b[0] {
      var i := 0;
      while i < b.Length
        // invariants-start

        // invariants-end
 {
        if a[i + p] != b[i] {
          return -1;
        }
        i := i + 1;
      }
      pos := p;
      return pos;
    }
    p := p + 1;
  }
// impl-end
}
