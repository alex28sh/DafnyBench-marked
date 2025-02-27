method mergeSimple(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  // pre-conditions-start
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires 0 <= start <= end <= b.Length
  requires |a1| + |a2| == end - start + 1
  // pre-conditions-end
  // post-conditions-start
  modifies b
  ensures sorted_slice(b, start, end)
  // post-conditions-end
{
// impl-start
  var a1Pos := 0;
  var a2Pos := 0;
  var k := start;
  while k < end
    // invariants-start

    invariant 0 <= k && k <= end
    invariant sorted_slice(b, start, k)
    invariant |a1| - a1Pos + (|a2| - a2Pos) == end - k + 1
    invariant 0 <= a1Pos <= |a1|
    invariant 0 <= a2Pos <= |a2|
    invariant forall i :: start <= i < k && a1Pos < |a1| ==> b[i] <= a1[a1Pos]
    invariant forall i :: start <= i < k && a2Pos < |a2| ==> b[i] <= a2[a2Pos]
    // invariants-end

  {
    if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] <= a2[a2Pos] {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] > a2[a2Pos] {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    } else if a1Pos < |a1| {
      // assert-start
      assert a2Pos >= |a2|;
      // assert-end

      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else {
      // assert-start
      assert a1Pos >= |a1|;
      // assert-end

      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    }
    k := k + 1;
  }
// impl-end
}

method merge(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
  // pre-conditions-start
  requires sorted_seq(a1)
  requires sorted_seq(a2)
  requires end - start == |a1| + |a2|
  requires 0 <= start < end < |a1| && end <= |a2| < b.Length
  requires end < |a1| && end < |a2|
  requires b.Length == |a2| + |a1|
  // pre-conditions-end
  // post-conditions-start
  modifies b
  ensures sorted_slice(b, start, end)
  ensures merged(a1, a2, b, start, end)
  // post-conditions-end
{
// impl-start
  // assert-start
  assert forall xs: seq<int> :: xs[0 .. |xs|] == xs;
  // assert-end

  // assert-start
  assert forall xs: seq<int>, a, b: int :: 0 <= a < b < |xs| ==> xs[a .. b + 1] == xs[a .. b] + [xs[b]];
  // assert-end

  var a1Pos := 0;
  var a2Pos := 0;
  var k := start;
  while k < end
    // invariants-start

    invariant 0 <= k && k <= end
    invariant sorted_slice(b, start, k)
    invariant |a1| - a1Pos + (|a2| - a2Pos) == end - k
    invariant 0 <= a1Pos <= |a1|
    invariant 0 <= a2Pos <= |a2|
    invariant forall i :: start <= i < k && a1Pos < |a1| ==> b[i] <= a1[a1Pos]
    invariant forall i :: start <= i < k && a2Pos < |a2| ==> b[i] <= a2[a2Pos]
    invariant merged(a1[0 .. a1Pos], a2[0 .. a2Pos], b, start, k)
    // invariants-end

  {
    if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] <= a2[a2Pos] {
      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else if a1Pos < |a1| && a2Pos < |a2| && a1[a1Pos] > a2[a2Pos] {
      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    } else if a1Pos < |a1| {
      // assert-start
      assert a2Pos >= |a2|;
      // assert-end

      b[k] := a1[a1Pos];
      a1Pos := a1Pos + 1;
    } else {
      // assert-start
      assert a1Pos >= |a1|;
      // assert-end

      b[k] := a2[a2Pos];
      a2Pos := a2Pos + 1;
    }
    k := k + 1;
  }
// impl-end
}

function merged(a1: seq<int>, a2: seq<int>, b: array<int>, start: int, end: int): bool
  requires end - start == |a2| + |a1|
  requires 0 <= start <= end <= b.Length
  reads b
{
  multiset(a1) + multiset(a2) == multiset(b[start .. end])
}
// pure-end

function sorted_slice(a: array<int>, start: int, end: int): bool
  requires 0 <= start <= end <= a.Length
  reads a
{
  forall i, j :: 
    start <= i <= j < end ==>
      a[i] <= a[j]
}
// pure-end

function sorted_seq(a: seq<int>): bool
{
  forall i, j :: 
    0 <= i <= j < |a| ==>
      a[i] <= a[j]
}
// pure-end

function sorted(a: array<int>): bool
  reads a
{
  forall i, j :: 
    0 <= i < j < a.Length ==>
      a[i] <= a[j]
}
// pure-end
