function derangement(s: seq<nat>): bool
{
  forall i :: 
    0 <= i < |s| ==>
      s[i] != i
}
// pure-end

function permutation(s: seq<nat>): bool
{
  forall i :: 
    0 <= i < |s| ==>
      i in s
}
// pure-end

function multisetRange(n: nat): multiset<nat>
{
  multiset(seq(n, i => i))
}
// pure-end

function distinct<A(==)>(s: seq<A>): bool
{
  forall x, y :: 
    x != y &&
    0 <= x <= y < |s| ==>
      s[x] != s[y]
}
// pure-end

method test()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var tests := [2, 0, 1];
  var tests2 := [0, 1, 2];
  var t4 := seq(3, i => i);
  var test3 := multisetRange(3);
  // assert-start
  assert t4 == tests2;
  // assert-end

  // assert-start
  assert 0 in t4;
  // assert-end

  // assert-start
  assert 0 in test3;
  // assert-end

  // assert-start
  assert multiset(tests) == multisetRange(3);
  // assert-end

  // assert-start
  assert derangement(tests);
  // assert-end

  // assert-start
  assert permutation(tests);
  // assert-end

  // assert-start
  assert permutation(tests2);
  // assert-end

// impl-end
}

method {:timelimit 40} end(links: seq<nat>)
  // pre-conditions-start
  requires |links| > 0
  requires permutation(links)
  requires derangement(links)
  requires distinct(links)
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assume forall x :: x in links ==> 0 <= x < |links|;
  // assert-end

  // assert-start
  assume forall x :: x in links ==> multiset(links)[x] == 1;
  // assert-end

  var qAct: nat := links[0];
  // assert-start
  assert links[0] in links;
  // assert-end

  var i: nat := 0;
  ghost var oldIndex := 0;
  ghost var indices: multiset<nat> := multiset{0};
  ghost var visited: multiset<nat> := multiset{};
  while qAct != 0
    // invariants-start

    invariant 0 <= oldIndex < |links|
    invariant qAct == links[oldIndex]
    invariant oldIndex in indices
    invariant qAct in links
    invariant indices == visited + multiset{0}
    invariant forall x :: x in visited ==> exists k :: 0 <= k < |links| && links[k] == x && k in indices
    invariant qAct !in visited
    invariant 0 <= qAct < |links|
    decreases multiset(links) - visited
    // invariants-end

  {
    ghost var oldVisit := visited;
    ghost var oldqAct := qAct;
    ghost var oldOldIndex := oldIndex;
    oldIndex := qAct;
    visited := visited + multiset{qAct};
    indices := indices + multiset{qAct};
    // assert-start
    assert oldqAct in visited;
    // assert-end

    // assert-start
    assert forall x :: x in visited ==> exists k :: 0 <= k < |links| && links[k] == x && k in indices;
    // assert-end

    qAct := links[qAct];
    i := i + 1;
  }
// impl-end
}
