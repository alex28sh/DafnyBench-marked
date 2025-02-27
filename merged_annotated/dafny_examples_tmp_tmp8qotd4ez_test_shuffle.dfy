method random(a: int, b: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a <= b ==> a <= r <= b
  // post-conditions-end

lemma eqMultiset_t<T>(t: T, s1: seq<T>, s2: seq<T>)
  // pre-conditions-start
  requires multiset(s1) == multiset(s2)
  // pre-conditions-end
  // post-conditions-start
  ensures t in s1 <==> t in s2
  // post-conditions-end
{
// impl-start
  calc <==> {
    t in s1;
    t in multiset(s1);
  }
// impl-end
}

lemma eqMultiset<T>(s1: seq<T>, s2: seq<T>)
  // pre-conditions-start
  requires multiset(s1) == multiset(s2)
  // pre-conditions-end
  // post-conditions-start
  ensures forall t :: t in s1 <==> t in s2
  // post-conditions-end
{
// impl-start
  forall t | true {
    eqMultiset_t(t, s1, s2);
  }
// impl-end
}

method swap<T>(a: array<T>, i: int, j: int)
  // pre-conditions-start
  requires 0 <= i < a.Length && 0 <= j < a.Length
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
  ensures multiset(a[..]) == old(multiset(a[..]))
  // post-conditions-end
{
// impl-start
  var t := a[i];
  a[i] := a[j];
  a[j] := t;
// impl-end
}

method getAllShuffledDataEntries<T(0)>(m_dataEntries: array<T>) returns (result: array<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures result.Length == m_dataEntries.Length
  ensures multiset(result[..]) == multiset(m_dataEntries[..])
  // post-conditions-end
{
// impl-start
  result := new T[m_dataEntries.Length];
  forall i | 0 <= i < m_dataEntries.Length {
    result[i] := m_dataEntries[i];
  }
  // assert-start
  assert result[..] == m_dataEntries[..];
  // assert-end

  var k := result.Length - 1;
  while k >= 0
    // invariants-start

    invariant multiset(result[..]) == multiset(m_dataEntries[..])
    // invariants-end

  {
    var i := random(0, k);
    // assert-start
    assert i >= 0 && i <= k;
    // assert-end

    if i != k {
      swap(result, i, k);
    }
    k := k - 1;
  }
// impl-end
}

function set_of_seq<T>(s: seq<T>): set<T>
{
  set x: T | x in s :: x
}
// pure-end

lemma in_set_of_seq<T>(x: T, s: seq<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures x in s <==> x in set_of_seq(s)
  // post-conditions-end

lemma subset_set_of_seq<T>(s1: seq<T>, s2: seq<T>)
  // pre-conditions-start
  requires set_of_seq(s1) <= set_of_seq(s2)
  // pre-conditions-end
  // post-conditions-start
  ensures forall x :: x in s1 ==> x in s2
  // post-conditions-end

method getRandomDataEntry<T(==)>(m_workList: array<T>, avoidSet: seq<T>) returns (e: T)
  // pre-conditions-start
  requires m_workList.Length > 0
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var k := m_workList.Length - 1;
  while k >= 0
    // invariants-start

    // invariants-end
 {
    var i := random(0, k);
    // assert-start
    assert i >= 0 && i <= k;
    // assert-end

    e := m_workList[i];
    if e !in avoidSet {
      return e;
    }
    k := k - 1;
  }
  return m_workList[0];
// impl-end
}
