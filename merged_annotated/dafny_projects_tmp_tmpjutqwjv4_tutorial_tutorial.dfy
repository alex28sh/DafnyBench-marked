// dafny_projects_tmp_tmpjutqwjv4_tutorial_tutorial.dfy

function fib(n: nat): nat
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    fib(n - 1) + fib(n - 2)
}
// pure-end

method ComputeFib(n: nat) returns (ret: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures ret == fib(n)
  // post-conditions-end
{
// impl-start
  var a := 0;
  var b := 1;
  var i := 0;
  while i < n
    // invariants-start

    invariant 0 <= i <= n
    invariant a == fib(i)
    invariant b == fib(i + 1)
    // invariants-end

  {
    a, b := b, a + b;
    i := i + 1;
  }
  // assert-start
  assert i == n;
  // assert-end

  return a;
// impl-end
}

method Find(a: array<int>, key: int) returns (index: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
  // post-conditions-end
{
// impl-start
  index := 0;
  while index < a.Length
    // invariants-start

    invariant 0 <= index <= a.Length
    invariant forall k :: 0 <= k < index ==> a[k] != key
    // invariants-end

  {
    if a[index] == key {
      return index;
    }
    index := index + 1;
  }
  return -1;
// impl-end
}

predicate sorted(a: array<int>)
  reads a
{
  forall n, m :: 
    0 <= n < m < a.Length ==>
      a[n] <= a[m]
}
// pure-end

method BinarySearch(a: array<int>, value: int) returns (index: int)
  // pre-conditions-start
  requires 0 <= a.Length && sorted(a)
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
  // post-conditions-end
{
// impl-start
  var low := 0;
  var high := a.Length - 1;
  while low < high
    // invariants-start

    invariant 0 <= low && high < a.Length
    invariant forall k :: 0 <= k < a.Length && (k < low || k > high) ==> a[k] != value
    // invariants-end

  {
    var mid: int := (low + high) / 2;
    // assert-start
    assert 0 <= low <= mid < high < a.Length;
    // assert-end

    if a[mid] < value {
      low := mid + 1;
    } else if a[mid] > value {
      high := mid - 1;
    } else {
      // assert-start
      assert a[mid] == value;
      // assert-end

      return mid;
    }
  }
  if low < a.Length && a[low] == value {
    return low;
  } else {
    return -1;
  }
// impl-end
}

function update(s: seq<int>, i: int, v: int): seq<int>
  requires 0 <= i < |s|
  ensures update(s, i, v) == s[i := v]
{
  s[..i] + [v] + s[i + 1..]
}
// pure-end

lemma SkippingLemma(a: array<int>, j: int)
  // pre-conditions-start
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i - 1] - 1 <= a[i]
  requires 0 <= j < a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: j <= i < j + a[j] && i < a.Length ==> a[i] != 0
  // post-conditions-end
{
// impl-start
  var i := j;
  while i < j + a[j] && i < a.Length
    invariant i < a.Length ==> a[i] >= a[j] - (i - j)
    invariant forall k :: j <= k < i && k < a.Length ==> a[k] != 0
  {
    i := i + 1;
  }
// impl-end
}

method FindZero(a: array<int>) returns (index: int)
  // pre-conditions-start
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i - 1] - 1 <= a[i]
  // pre-conditions-end
  // post-conditions-start
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
  // post-conditions-end
{
// impl-start
  index := 0;
  while index < a.Length
    // invariants-start

    invariant 0 <= index
    invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != 0
    // invariants-end

  {
    if a[index] == 0 {
      return;
    }
    // assert-start
    SkippingLemma(a, index);
    // assert-end

    index := index + a[index];
  }
  index := -1;
// impl-end
}

function count(a: seq<bool>): nat
{
  if |a| == 0 then
    0
  else
    (if a[0] then 1 else 0) + count(a[1..])
}
// pure-end

lemma DistributiveLemma(a: seq<bool>, b: seq<bool>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures count(a + b) == count(a) + count(b)
  // post-conditions-end
{
// impl-start
  if a == [] {
    assert a + b == b;
  } else {
    assert a + b == [a[0]] + (a[1..] + b);
  }
// impl-end
}

predicate closed(graph: set<Node>)
  reads graph
{
  forall i :: 
    i in graph ==>
      forall k :: 
        0 <= k < |i.next| ==>
          i.next[k] in graph &&
          i.next[k] != i
}
// pure-end

predicate path(p: seq<Node>, graph: set<Node>)
  requires closed(graph) && 0 < |p|
  reads graph
{
  p[0] in graph &&
  (|p| > 1 ==>
    p[1] in p[0].next &&
    path(p[1..], graph))
}
// pure-end

predicate pathSpecific(p: seq<Node>, start: Node, end: Node, graph: set<Node>)
  requires closed(graph)
  reads graph
{
  0 < |p| &&
  start == p[0] &&
  end == p[|p| - 1] &&
  path(p, graph)
}
// pure-end

lemma DisproofLemma(p: seq<Node>, subgraph: set<Node>, root: Node, goal: Node, graph: set<Node>)
  // pre-conditions-start
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  // pre-conditions-end
  // post-conditions-start
  ensures !pathSpecific(p, root, goal, graph)
  // post-conditions-end
{
// impl-start
  if |p| >= 2 && p[0] == root && p[1] in p[0].next {
    DisproofLemma(p[1..], subgraph, p[1], goal, graph);
  }
// impl-end
}

lemma ClosedLemma(subgraph: set<Node>, root: Node, goal: Node, graph: set<Node>)
  // pre-conditions-start
  requires closed(subgraph) && closed(graph) && subgraph <= graph
  requires root in subgraph && goal in graph - subgraph
  // pre-conditions-end
  // post-conditions-start
  ensures !exists p: seq<Node> :: pathSpecific(p, root, goal, graph)
  // post-conditions-end
{
// impl-start
  forall p | true {
    DisproofLemma(p, subgraph, root, goal, graph);
  }
// impl-end
}

class Node {
  var next: seq<Node>
}
