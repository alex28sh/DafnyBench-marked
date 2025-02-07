function SetLessThan(numbers: set<int>, threshold: int): set<int>
{
  set i | i in numbers && i < threshold
}
// pure-end

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var t: seq<int> := [1, 2, 3];
  var s: set<int> := {1, 2, 3};
  // assert-start
  assert |s| == 3;
  // assert-end

  // assert-start
  assert |s| == |t|;
  // assert-end

  s := set x | x in t;
  // assert-start
  assert forall x :: x in t ==> x in s;
  // assert-end

  // assert-start
  assert forall x :: x in s ==> x in t;
  // assert-end

  // assert-start
  assert forall x :: x in s <==> x in t;
  // assert-end

  // assert-start
  assert forall i, j :: 0 <= i < |t| && 0 <= j < |t| && i != j ==> t[i] != t[j];
  // assert-end

  // assert-start
  assert |t| == 3;
  // assert-end

  // assert-start
  set_memebrship_implies_cardinality(s, set x | x in t);
  // assert-end

  var s2: set<int> := set x | x in t;
  // assert-start
  assert |s| == |s2|;
  // assert-end

  s2 := {1, 2, 3};
  // assert-start
  set_memebrship_implies_cardinality(s, s2);
  // assert-end

  // assert-start
  assert |s| == |s2|;
  // assert-end

// impl-end
}

lemma set_memebrship_implies_cardinality_helper<A>(s: set<A>, t: set<A>, s_size: int)
  // pre-conditions-start
  requires s_size >= 0 && s_size == |s|
  requires forall x :: x in s <==> x in t
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  decreases s_size
  // post-conditions-end
{
// impl-start
  if s_size == 0 {
  } else {
    var s_hd;
    s_hd :| s_hd in s;
    set_memebrship_implies_cardinality_helper(s - {s_hd}, t - {s_hd}, s_size - 1);
  }
// impl-end
}

lemma set_memebrship_implies_cardinality<A>(s: set<A>, t: set<A>)
  // pre-conditions-start
  requires forall x :: x in s <==> x in t
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  // post-conditions-end
{
// impl-start
  set_memebrship_implies_cardinality_helper(s, t, |s|);
// impl-end
}

function seqSet(nums: seq<int>, index: nat): set<int>
{
  set x | 0 <= x < index < |nums| :: nums[x]
}
// pure-end

lemma containsDuplicateI(nums: seq<int>) returns (containsDuplicate: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures containsDuplicate ==> exists i, j :: 0 <= i < j < |nums| && nums[i] == nums[j]
  // post-conditions-end
{
// impl-start
  var windowGhost: set<int> := {};
  var windowSet: set<int> := {};
  for i := 0 to |nums|
    invariant 0 <= i <= |nums|
    invariant forall j :: 0 <= j < i < |nums| ==> nums[j] in windowSet
    invariant forall x :: x in windowSet ==> x in nums[0 .. i]
    invariant seqSet(nums, i) <= windowSet
  {
    windowGhost := windowSet;
    if nums[i] in windowSet {
      return true;
    }
    windowSet := windowSet + {nums[i]};
  }
  return false;
// impl-end
}

lemma set_memebrship_implies_equality_helper<A>(s: set<A>, t: set<A>, s_size: int)
  // pre-conditions-start
  requires s_size >= 0 && s_size == |s|
  requires forall x :: x in s <==> x in t
  // pre-conditions-end
  // post-conditions-start
  ensures s == t
  decreases s_size
  // post-conditions-end
{
// impl-start
  if s_size == 0 {
  } else {
    var s_hd;
    s_hd :| s_hd in s;
    set_memebrship_implies_equality_helper(s - {s_hd}, t - {s_hd}, s_size - 1);
  }
// impl-end
}

lemma set_memebrship_implies_equality<A>(s: set<A>, t: set<A>)
  // pre-conditions-start
  requires forall x :: x in s <==> x in t
  // pre-conditions-end
  // post-conditions-start
  ensures s == t
  // post-conditions-end
{
// impl-start
  set_memebrship_implies_equality_helper(s, t, |s|);
// impl-end
}

lemma set_seq_equality(s: set<int>, t: seq<int>)
  // pre-conditions-start
  requires distinct(t)
  requires forall x :: x in t <==> x in s
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var s2: set<int> := set x | x in t;
  set_memebrship_implies_equality_helper(s, s2, |s|);
  assert |s2| == |s|;
// impl-end
}

function SortedSeq(a: seq<int>): bool
{
  forall i, j :: 
    0 <= i < j < |a| ==>
      a[i] < a[j]
}
// pure-end

method GetInsertIndex(a: array<int>, limit: int, x: int)
    returns (idx: int)
  // pre-conditions-start
  requires x !in a[..]
  requires 0 <= limit <= a.Length
  requires SortedSeq(a[..limit])
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= idx <= limit
  ensures SortedSeq(a[..limit])
  ensures idx > 0 ==> a[idx - 1] < x
  ensures idx < limit ==> x < a[idx]
  // post-conditions-end
{
// impl-start
  idx := limit;
  for i := 0 to limit
    // invariants-start

    invariant i > 0 ==> x > a[i - 1]
    // invariants-end

  {
    if x < a[i] {
      idx := i;
      break;
    }
  }
// impl-end
}

function sorted(a: seq<int>): bool
{
  forall i, j :: 
    0 <= i < j < |a| ==>
      a[i] < a[j]
}
// pure-end

function distinct(a: seq<int>): bool
{
  forall i, j :: 
    0 <= i < |a| &&
    0 <= j < |a| &&
    i != j ==>
      a[i] != a[j]
}
// pure-end

function sorted_eq(a: seq<int>): bool
{
  forall i, j :: 
    0 <= i < j < |a| ==>
      a[i] <= a[j]
}
// pure-end

function lessThan(a: seq<int>, key: int): bool
{
  forall i :: 
    0 <= i < |a| ==>
      a[i] < key
}
// pure-end

function greaterThan(a: seq<int>, key: int): bool
{
  forall i :: 
    0 <= i < |a| ==>
      a[i] > key
}
// pure-end

function greaterEqualThan(a: seq<int>, key: int): bool
{
  forall i :: 
    0 <= i < |a| ==>
      a[i] >= key
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
    DistributiveLemma(a[1..], b);
    assert a + b == [a[0]] + (a[1..] + b);
  }
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

lemma DistributiveIn(a: seq<int>, b: seq<int>, k: int, key: int)
  // pre-conditions-start
  requires |a| + 1 == |b|
  requires 0 <= k <= |a|
  requires b == a[..k] + [key] + a[k..]
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |a| ==> a[i] in b
  // post-conditions-end
{
// impl-start
  assert forall j :: 0 <= j < k ==> a[j] in b;
  assert forall j :: k <= j < |a| ==> a[j] in b;
  assert (forall j :: 0 <= j < k ==> a[j] in b) && (forall j :: k <= j < |a| ==> a[j] in b) ==> forall j :: 0 <= j < |a| ==> a[j] in b;
  assert forall j :: 0 <= j < |a| ==> a[j] in b;
// impl-end
}

lemma DistributiveGreater(a: seq<int>, b: seq<int>, k: int, key: int)
  // pre-conditions-start
  requires |a| + 1 == |b|
  requires 0 <= k <= |a|
  requires b == a[..k] + [key] + a[k..]
  requires forall j :: 0 <= j < |a| ==> a[j] > 0
  requires key > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |b| ==> b[i] > 0
  // post-conditions-end
{
// impl-start
  assert forall j :: 0 <= j < |b| ==> b[j] > 0;
// impl-end
}

method InsertIntoSorted(a: array<int>, limit: int, key: int)
    returns (b: array<int>)
  // pre-conditions-start
  requires key > 0
  requires key !in a[..]
  requires 0 <= limit < a.Length
  requires forall i :: 0 <= i < limit ==> a[i] > 0
  requires forall i :: limit <= i < a.Length ==> a[i] == 0
  requires sorted(a[..limit])
  // pre-conditions-end
  // post-conditions-start
  ensures b.Length == a.Length
  ensures sorted(b[..limit + 1])
  ensures forall i :: limit + 1 <= i < b.Length ==> b[i] == 0
  ensures forall i :: 0 <= i < limit ==> a[i] in b[..]
  ensures forall i :: 0 <= i < limit + 1 ==> b[i] > 0
  // post-conditions-end
{
// impl-start
  b := new int[a.Length];
  ghost var k := 0;
  b[0] := key;
  ghost var a' := a[..];
  var i := 0;
  while i < limit
    // invariants-start

    invariant 0 <= k <= i <= limit
    invariant b.Length == a.Length
    invariant a[..] == a'
    invariant lessThan(a[..i], key) ==> i == k
    invariant lessThan(a[..k], key)
    invariant b[..k] == a[..k]
    invariant b[k] == key
    invariant k < i ==> b[k + 1 .. i + 1] == a[k .. i]
    invariant k < i ==> greaterThan(b[k + 1 .. i + 1], key)
    invariant 0 <= k < b.Length && b[k] == key
    modifies b
    // invariants-end

  {
    if a[i] < key {
      b[i] := a[i];
      b[i + 1] := key;
      k := i + 1;
    } else if a[i] >= key {
      b[i + 1] := a[i];
    }
    i := i + 1;
  }
  // assert-start
  assert b[..limit + 1] == a[..k] + [key] + a[k .. limit];
  // assert-end

  // assert-start
  assert sorted(b[..limit + 1]);
  // assert-end

  // assert-start
  DistributiveIn(a[..limit], b[..limit + 1], k, key);
  // assert-end

  // assert-start
  assert forall i :: 0 <= i < limit ==> a[i] in b[..limit + 1];
  // assert-end

  // assert-start
  DistributiveGreater(a[..limit], b[..limit + 1], k, key);
  // assert-end

  ghost var b' := b[..];
  i := limit + 1;
  while i < b.Length
    // invariants-start

    invariant limit + 1 <= i <= b.Length
    invariant forall j :: limit + 1 <= j < i ==> b[j] == 0
    invariant b[..limit + 1] == b'[..limit + 1]
    invariant sorted(b[..limit + 1])
    // invariants-end

  {
    b[i] := 0;
    i := i + 1;
  }
  // assert-start
  assert forall i :: limit + 1 <= i < b.Length ==> b[i] == 0;
  // assert-end

// impl-end
}
