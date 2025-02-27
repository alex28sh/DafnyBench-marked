lemma BinarySearch(intSeq: seq<int>, key: int) returns (r: int)
  // pre-conditions-start
  requires forall i, j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  // pre-conditions-end
  // post-conditions-start
  ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
  ensures r < 0 ==> forall i: nat | i < |intSeq| :: intSeq[i] != key
  // post-conditions-end
{
// impl-start
  var lo: nat := 0;
  var hi: nat := |intSeq|;
  while lo < hi
    invariant 0 <= lo <= hi <= |intSeq|
    invariant forall i: nat | 0 <= i < lo :: intSeq[i] < key
    invariant forall i: nat | hi <= i < |intSeq| :: intSeq[i] > key
  {
    var mid := (lo + hi) / 2;
    if intSeq[mid] < key {
      lo := mid + 1;
    } else if intSeq[mid] > key {
      hi := mid;
    } else {
      return mid;
    }
  }
  return -1;
// impl-end
}

function BinarySearchTransition(intSeq: seq<int>, key: int, r: int): bool
  requires forall i, j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
  (r >= 0 ==>
    r < |intSeq| &&
    intSeq[r] == key) &&
  (r < 0 ==>
    forall i: nat | i < |intSeq| :: 
      intSeq[i] != key)
}
// pure-end

lemma BinarySearchDeterministic(intSeq: seq<int>, key: int) returns (r: int)
  // pre-conditions-start
  requires forall i, j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  // pre-conditions-end
  // post-conditions-start
  ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
  ensures r < 0 ==> forall i: nat | i < |intSeq| :: intSeq[i] != key
  ensures r < 0 ==> r == -1
  ensures r >= 0 ==> forall i: nat | i < r :: intSeq[i] < key
  // post-conditions-end
{
// impl-start
  var lo: nat := 0;
  var hi: nat := |intSeq|;
  while lo < hi
    invariant 0 <= lo <= hi <= |intSeq|
    invariant forall i: nat | 0 <= i < lo :: intSeq[i] < key
    invariant (forall i: nat | hi <= i < |intSeq| :: intSeq[i] > key) || forall i: nat | hi <= i < |intSeq| :: intSeq[i] >= key && exists i: nat | lo <= i < hi :: intSeq[i] == key
  {
    var mid := (lo + hi) / 2;
    if intSeq[mid] < key {
      lo := mid + 1;
    } else if intSeq[mid] > key {
      hi := mid;
    } else {
      assert intSeq[mid] == key;
      var inner_mid := (lo + mid) / 2;
      if intSeq[inner_mid] < key {
        lo := inner_mid + 1;
      } else if hi != inner_mid + 1 {
        hi := inner_mid + 1;
      } else {
        if intSeq[lo] == key {
          return lo;
        } else {
          lo := lo + 1;
        }
      }
    }
  }
  return -1;
// impl-end
}

function BinarySearchDeterministicTransition(intSeq: seq<int>, key: int, r: int): bool
  requires forall i, j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
  (r >= 0 ==>
    r < |intSeq| &&
    intSeq[r] == key) &&
  (r < 0 ==>
    forall i: nat | i < |intSeq| :: 
      intSeq[i] != key) &&
  (r < 0 ==>
    r == -1) &&
  (r >= 0 ==>
    forall i: nat | i < r :: 
      intSeq[i] < key)
}
// pure-end

lemma BinarySearchWrong1(intSeq: seq<int>, key: int) returns (r: int)
  // pre-conditions-start
  requires forall i, j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  // pre-conditions-end
  // post-conditions-start
  ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
  ensures r < 0 ==> forall i: nat | 0 < i < |intSeq| :: intSeq[i] != key
  ensures r < 0 ==> r == -1
  ensures r >= 0 ==> forall i: nat | i < r :: intSeq[i] < key
  // post-conditions-end

function BinarySearchWrong1Transition(intSeq: seq<int>, key: int, r: int): bool
  requires forall i, j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
  (r >= 0 ==>
    r < |intSeq| &&
    intSeq[r] == key) &&
  (r < 0 ==>
    forall i: nat | 0 < i < |intSeq| :: 
      intSeq[i] != key) &&
  (r < 0 ==>
    r == -1) &&
  (r >= 0 ==>
    forall i: nat | i < r :: 
      intSeq[i] < key)
}
// pure-end

lemma BinarySearchWrong2(intSeq: seq<int>, key: int) returns (r: int)
  // pre-conditions-start
  requires forall i, j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  // pre-conditions-end
  // post-conditions-start
  ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
  ensures r < 0 ==> forall i: nat | 0 <= i < |intSeq| - 1 :: intSeq[i] != key
  ensures r < 0 ==> r == -1
  ensures r >= 0 ==> forall i: nat | i < r :: intSeq[i] < key
  // post-conditions-end

function BinarySearchWrong2Transition(intSeq: seq<int>, key: int, r: int): bool
  requires forall i, j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
  (r >= 0 ==>
    r < |intSeq| &&
    intSeq[r] == key) &&
  (r < 0 ==>
    forall i: nat | 0 <= i < |intSeq| - 1 :: 
      intSeq[i] != key) &&
  (r < 0 ==>
    r == -1) &&
  (r >= 0 ==>
    forall i: nat | i < r :: 
      intSeq[i] < key)
}
// pure-end

lemma BinarySearchWrong3(intSeq: seq<int>, key: int) returns (r: int)
  // pre-conditions-start
  requires forall i, j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  // pre-conditions-end
  // post-conditions-start
  ensures r < 0 || (r < |intSeq| && intSeq[r] == key)
  // post-conditions-end
{
// impl-start
  return -1;
// impl-end
}

function BinarySearchWrong3Transition(intSeq: seq<int>, key: int, r: int): bool
  requires forall i, j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
  r < 0 || (r < |intSeq| && intSeq[r] == key)
}
// pure-end

lemma BinarySearchWrong4(intSeq: seq<int>, key: int) returns (r: int)
  // pre-conditions-start
  requires forall i, j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= r < |intSeq| && intSeq[r] == key
  // post-conditions-end

function BinarySearchWrong4Transition(intSeq: seq<int>, key: int, r: int): bool
  requires forall i, j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
  0 <= r < |intSeq| &&
  intSeq[r] == key
}
// pure-end
