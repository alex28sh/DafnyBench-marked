method Foo(y: int, x: int) returns (z: int)
  // pre-conditions-start
  requires 0 <= y
  // pre-conditions-end
  // post-conditions-start
  ensures z == x * y
  // post-conditions-end
{
// impl-start
  var a: int := 0;
  z := 0;
  while a != y
    // invariants-start

    invariant 0 <= a <= y
    invariant z == a * x
    decreases y - a
    // invariants-end

  {
    z := z + x;
    a := a + 1;
  }
  return z;
// impl-end
}

function stringToSet(s: string): (r: set<char>)
  ensures forall x :: 0 <= x < |s| ==> s[x] in r
{
  set x | 0 <= x < |s| :: s[x]
}
// pure-end

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var sample: string := "test";
  var foof := Foo(3, 4);
  var test: set<char> := stringToSet(sample);
  // assert-start
  assert test == stringToSet(sample);
  // assert-end

  // assert-start
  assert forall x :: 0 <= x < |sample| ==> sample[x] in test;
  // assert-end

  // assert-start
  assert 't' in sample;
  // assert-end

  // assert-start
  assert 't' in test;
  // assert-end

  print foof;
// impl-end
}
