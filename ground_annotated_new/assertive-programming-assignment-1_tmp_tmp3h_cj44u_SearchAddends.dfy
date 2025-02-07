method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var q := [1, 2, 4, 5, 6, 7, 10, 23];
  // assert-start
  assert Sorted(q);
  // assert-end

  // assert-start
  assert HasAddends(q, 10) by {
    assert q[2] + q[4] == 4 + 6 == 10;
  }
  // assert-end

  var i, j := FindAddends(q, 10);
  print "Searching for addends of 10 in q == [1,2,4,5,6,7,10,23]:\n";
  print "Found that q[";
  print i;
  print "] + q[";
  print j;
  print "] == ";
  print q[i];
  print " + ";
  print q[j];
  print " == 10";
  // assert-start
  assert i == 2 && j == 4;
  // assert-end

// impl-end
}

function Sorted(q: seq<int>): bool
{
  forall i, j :: 
    0 <= i <= j < |q| ==>
      q[i] <= q[j]
}
// pure-end

function HasAddends(q: seq<int>, x: int): bool
{
  exists i, j :: 
    0 <= i < j < |q| &&
    q[i] + q[j] == x
}
// pure-end

method FindAddends(q: seq<int>, x: int)
    returns (i: nat, j: nat)
  // pre-conditions-start
  requires Sorted(q) && HasAddends(q, x)
  // pre-conditions-end
  // post-conditions-start
  ensures i < j < |q| && q[i] + q[j] == x
  // post-conditions-end
{
// impl-start
  i := 0;
  j := |q| - 1;
  var sum := q[i] + q[j];
  while sum != x
    // invariants-start

    invariant LoopInv(q, x, i, j, sum)
    decreases j - i
    // invariants-end

  {
    if sum > x {
      // assert-start
      LoopInvWhenSumIsBigger(q, x, i, j, sum);
      // assert-end

      j := j - 1;
    } else {
      i := i + 1;
    }
    sum := q[i] + q[j];
  }
// impl-end
}

function IsValidIndex<T>(q: seq<T>, i: nat): bool
{
  0 <= i < |q|
}
// pure-end

function AreOreredIndices<T>(q: seq<T>, i: nat, j: nat): bool
{
  0 <= i < j < |q|
}
// pure-end

function AreAddendsIndices(q: seq<int>, x: int, i: nat, j: nat): bool
  requires IsValidIndex(q, i) && IsValidIndex(q, j)
{
  q[i] + q[j] == x
}
// pure-end

function HasAddendsInIndicesRange(q: seq<int>, x: int, i: nat, j: nat): bool
  requires AreOreredIndices(q, i, j)
{
  HasAddends(q[i .. j + 1], x)
}
// pure-end

function LoopInv(q: seq<int>, x: int, i: nat, j: nat, sum: int): bool
{
  AreOreredIndices(q, i, j) &&
  HasAddendsInIndicesRange(q, x, i, j) &&
  AreAddendsIndices(q, sum, i, j)
}
// pure-end

lemma LoopInvWhenSumIsBigger(q: seq<int>, x: int, i: nat, j: nat, sum: int)
  // pre-conditions-start
  requires HasAddends(q, x)
  requires Sorted(q)
  requires sum > x
  requires LoopInv(q, x, i, j, sum)
  // pre-conditions-end
  // post-conditions-start
  ensures HasAddendsInIndicesRange(q, x, i, j - 1)
  // post-conditions-end
{
// impl-start
  assert q[i .. j] < q[i .. j + 1];
// impl-end
}
