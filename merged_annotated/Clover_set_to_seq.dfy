method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures multiset(s) == multiset(xs)
  // post-conditions-end
{
// impl-start
  xs := [];
  var left: set<T> := s;
  while left != {}
    // invariants-start

    invariant multiset(left) + multiset(xs) == multiset(s)
    // invariants-end

  {
    var x :| x in left;
    left := left - {x};
    xs := xs + [x];
  }
// impl-end
}
