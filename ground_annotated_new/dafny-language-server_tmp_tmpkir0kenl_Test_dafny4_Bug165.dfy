function f(a: T): bool
// pure-end

method Select(s1: seq<T>) returns (r: seq<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall e: T :: f(e) ==> multiset(s1)[e] == multiset(r)[e]
  ensures forall e: T :: !f(e) ==> 0 == multiset(r)[e]
  // post-conditions-end

method Main(s1: seq<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var r1, r2: seq<T>;
  r1 := Select(s1);
  r2 := Select(s1);
  // assert-start
  assert multiset(r1) == multiset(r2);
  // assert-end

// impl-end
}

type T(!new)
