method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var q := [1, 2, 2, 5, 10, 10, 10, 23];
  // assert-start
  assert Sorted(q);
  // assert-end

  // assert-start
  assert 10 in q;
  // assert-end

  var i, j := FindRange(q, 10);
  print "The number of occurrences of 10 in the sorted sequence [1,2,2,5,10,10,10,23] is ";
  print j - i;
  print " (starting at index ";
  print i;
  print " and ending in ";
  print j;
  print ").\n";
  // assert-start
  assert i == 4 && j == 7 by {
    assert q[0] <= q[1] <= q[2] <= q[3] < 10;
    assert q[4] == q[5] == q[6] == 10;
    assert 10 < q[7];
  }
  // assert-end

  q := [0, 1, 2];
  // assert-start
  assert Sorted(q);
  // assert-end

  i, j := FindRange(q, 10);
  print "The number of occurrences of 10 in the sorted sequence [0,1,2] is ";
  print j - i;
  print " (starting at index ";
  print i;
  print " and ending in ";
  print j;
  print ").\n";
  q := [10, 11, 12];
  // assert-start
  assert Sorted(q);
  // assert-end

  i, j := FindRange(q, 1);
  print "The number of occurrences of 1  in the sorted sequence [10,11,12] is ";
  print j - i;
  print " (starting at index ";
  print i;
  print " and ending in ";
  print j;
  print ").\n";
  q := [1, 11, 22];
  // assert-start
  assert Sorted(q);
  // assert-end

  i, j := FindRange(q, 10);
  print "The number of occurrences of 10 in the sorted sequence [1,11,22] is ";
  print j - i;
  print " (starting at index ";
  print i;
  print " and ending in ";
  print j;
  print ").\n";
  q := [1, 11, 22];
  // assert-start
  assert Sorted(q);
  // assert-end

  i, j := FindRange(q, 11);
  print "The number of occurrences of 11 in the sorted sequence [1,11,22] is ";
  print j - i;
  print " (starting at index ";
  print i;
  print " and ending in ";
  print j;
  print ").\n";
  q := [1, 11, 11];
  // assert-start
  assert Sorted(q);
  // assert-end

  i, j := FindRange(q, 11);
  print "The number of occurrences of 11 in the sorted sequence [1,11,11] is ";
  print j - i;
  print " (starting at index ";
  print i;
  print " and ending in ";
  print j;
  print ").\n";
  q := [11, 11, 14];
  // assert-start
  assert Sorted(q);
  // assert-end

  i, j := FindRange(q, 11);
  print "The number of occurrences of 11 in the sorted sequence [11 ,11, 14] is ";
  print j - i;
  print " (starting at index ";
  print i;
  print " and ending in ";
  print j;
  print ").\n";
  q := [1, 11, 11, 11, 13];
  // assert-start
  assert Sorted(q);
  // assert-end

  i, j := FindRange(q, 11);
  print "The number of occurrences of 11 in the sorted sequence [1,11,11,11,13] is ";
  print j - i;
  print " (starting at index ";
  print i;
  print " and ending in ";
  print j;
  print ").\n";
  q := [];
  // assert-start
  assert Sorted(q);
  // assert-end

  i, j := FindRange(q, 11);
  print "The number of occurrences of 11 in the sorted sequence [] is ";
  print j - i;
  print " (starting at index ";
  print i;
  print " and ending in ";
  print j;
  print ").\n";
  q := [11];
  // assert-start
  assert Sorted(q);
  // assert-end

  i, j := FindRange(q, 10);
  print "The number of occurrences of 10 in the sorted sequence [11] is ";
  print j - i;
  print " (starting at index ";
  print i;
  print " and ending in ";
  print j;
  print ").\n";
  q := [11];
  // assert-start
  assert Sorted(q);
  // assert-end

  i, j := FindRange(q, 11);
  print "The number of occurrences of 11 in the sorted sequence [11] is ";
  print j - i;
  print " (starting at index ";
  print i;
  print " and ending in ";
  print j;
  print ").\n";
// impl-end
}

function Sorted(q: seq<int>): bool
{
  forall i, j :: 
    0 <= i <= j < |q| ==>
      q[i] <= q[j]
}
// pure-end

method {:verify true} FindRange(q: seq<int>, key: int)
    returns (left: nat, right: nat)
  // pre-conditions-start
  requires Sorted(q)
  // pre-conditions-end
  // post-conditions-start
  ensures left <= right <= |q|
  ensures forall i :: 0 <= i < left ==> q[i] < key
  ensures forall i :: left <= i < right ==> q[i] == key
  ensures forall i :: right <= i < |q| ==> q[i] > key
  // post-conditions-end
{
// impl-start
  left := BinarySearch(q, key, 0, |q|, (n, m) => n >= m);
  right := BinarySearch(q, key, left, |q|, (n, m) => n > m);
// impl-end
}

function RangeSatisfiesComparer(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool): bool
  requires 0 <= lowerBound <= upperBound <= |q|
{
  forall i :: 
    lowerBound <= i < upperBound ==>
      comparer(q[i], key)
}
// pure-end

function RangeSatisfiesComparerNegation(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool): bool
  requires 0 <= lowerBound <= upperBound <= |q|
{
  RangeSatisfiesComparer(q, key, lowerBound, upperBound, (n1, n2) => !comparer(n1, n2))
}
// pure-end

method BinarySearch(q: seq<int>, key: int, lowerBound: nat, upperBound: nat, comparer: (int, int) -> bool)
    returns (index: nat)
  // pre-conditions-start
  requires Sorted(q)
  requires 0 <= lowerBound <= upperBound <= |q|
  requires RangeSatisfiesComparerNegation(q, key, 0, lowerBound, comparer)
  requires RangeSatisfiesComparer(q, key, upperBound, |q|, comparer)
  requires (forall n1, n2 :: comparer(n1, n2) == (n1 > n2)) || forall n1, n2 :: comparer(n1, n2) == (n1 >= n2)
  // pre-conditions-end
  // post-conditions-start
  ensures lowerBound <= index <= upperBound
  ensures RangeSatisfiesComparerNegation(q, key, 0, index, comparer)
  ensures RangeSatisfiesComparer(q, key, index, |q|, comparer)
  // post-conditions-end
{
// impl-start
  var low: nat := lowerBound;
  var high: nat := upperBound;
  while low < high
    // invariants-start

    invariant lowerBound <= low <= high <= upperBound
    invariant RangeSatisfiesComparerNegation(q, key, 0, low, comparer)
    invariant RangeSatisfiesComparer(q, key, high, |q|, comparer)
    decreases high - low
    // invariants-end

  {
    var middle := low + (high - low) / 2;
    if comparer(q[middle], key) {
      high := middle;
    } else {
      low := middle + 1;
    }
  }
  index := high;
// impl-end
}
