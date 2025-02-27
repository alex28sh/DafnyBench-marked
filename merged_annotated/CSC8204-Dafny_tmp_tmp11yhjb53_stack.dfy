function isEmpty(s: intStack): bool
{
  |s| == 0
}
// pure-end

function push(s: intStack, x: int): intStack
{
  s + [x]
}
// pure-end

function pop(s: intStack): intStack
  requires !isEmpty(s)
{
  s[..|s| - 1]
}
// pure-end

method testStack() returns (r: intStack)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var s: intStack := [20, 30, 15, 40, 60, 100, 80];
  // assert-start
  assert pop(push(s, 100)) == s;
  // assert-end

  // assert-start
  assert forall e: int :: 0 <= e < |s| ==> s[e] > 5;
  // assert-end

  r := s;
// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var t := testStack();
  print "Stack tested\nStack is ", t, "\n";
// impl-end
}

type intStack = seq<int>
