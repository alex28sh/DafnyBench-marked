method quickSort(intSeq: array<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies intSeq
  ensures forall i: nat, j: nat | 0 <= i <= j < intSeq.Length :: intSeq[i] <= intSeq[j]
  // post-conditions-end

lemma sort(prevSeq: seq<int>) returns (curSeq: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall i: nat, j: nat | 0 <= i <= j < |curSeq| :: curSeq[i] <= curSeq[j]
  ensures multiset(prevSeq) == multiset(curSeq)
  // post-conditions-end

function post_sort(prevSeq: seq<int>, curSeq: seq<int>): bool
{
  (forall i: nat, j: nat | 0 <= i <= j < |curSeq| :: 
    curSeq[i] <= curSeq[j]) &&
  multiset(prevSeq) == multiset(curSeq)
}
// pure-end

lemma multisetAdditivity(m1: multiset<int>, m2: multiset<int>, m3: multiset<int>, m4: multiset<int>)
  // pre-conditions-start
  requires m1 == m2 + m3
  requires m1 == m2 + m4
  // pre-conditions-end
  // post-conditions-start
  ensures m3 == m4
  // post-conditions-end
{
// impl-start
  assert m3 == m1 - m2;
  assert m4 == m1 - m2;
// impl-end
}

lemma twoSortedSequencesWithSameElementsAreEqual(s1: seq<int>, s2: seq<int>)
  // pre-conditions-start
  requires forall i: nat, j: nat | 0 <= i <= j < |s1| :: s1[i] <= s1[j]
  requires forall i: nat, j: nat | 0 <= i <= j < |s2| :: s2[i] <= s2[j]
  requires multiset(s1) == multiset(s2)
  requires |s1| == |s2|
  // pre-conditions-end
  // post-conditions-start
  ensures s1 == s2
  // post-conditions-end
{
// impl-start
  if |s1| != 0 {
    if s1[|s1| - 1] == s2[|s2| - 1] {
      assert multiset(s1[..|s1| - 1]) == multiset(s2[..|s2| - 1]) by {
        assert s1 == s1[..|s1| - 1] + [s1[|s1| - 1]];
        assert multiset(s1) == multiset(s1[..|s1| - 1]) + multiset([s1[|s1| - 1]]);
        assert s2 == s2[..|s1| - 1] + [s2[|s1| - 1]];
        assert multiset(s2) == multiset(s2[..|s1| - 1]) + multiset([s2[|s1| - 1]]);
        assert multiset([s1[|s1| - 1]]) == multiset([s2[|s1| - 1]]);
        multisetAdditivity(multiset(s1), multiset([s1[|s1| - 1]]), multiset(s1[..|s1| - 1]), multiset(s2[..|s1| - 1]));
      }
      twoSortedSequencesWithSameElementsAreEqual(s1[..|s1| - 1], s2[..|s2| - 1]);
    } else if s1[|s1| - 1] < s2[|s2| - 1] {
      assert s2[|s2| - 1] !in multiset(s1);
      assert false;
    } else {
      assert s1[|s1| - 1] !in multiset(s2);
      assert false;
    }
  }
// impl-end
}

lemma sort_determinisitc(prevSeq: seq<int>, curSeq: seq<int>, curSeq': seq<int>)
  // pre-conditions-start
  requires post_sort(prevSeq, curSeq)
  requires post_sort(prevSeq, curSeq')
  // pre-conditions-end
  // post-conditions-start
  ensures curSeq == curSeq'
  // post-conditions-end
{
// impl-start
  if |curSeq| != |curSeq'| {
    assert |multiset(curSeq)| != |multiset(curSeq')|;
  } else {
    twoSortedSequencesWithSameElementsAreEqual(curSeq, curSeq');
  }
// impl-end
}

lemma sort_determinisitc1(prevSeq: seq<int>, curSeq: seq<int>, curSeq': seq<int>)
  // pre-conditions-start
  requires prevSeq == [5, 4, 3, 2, 1]
  requires post_sort(prevSeq, curSeq)
  requires post_sort(prevSeq, curSeq')
  // pre-conditions-end
  // post-conditions-start
  ensures curSeq == curSeq'
  // post-conditions-end
{
// impl-start
// impl-end
}
