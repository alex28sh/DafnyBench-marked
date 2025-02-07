function sorted(a: array<T>): bool
  reads a
{
  forall i, j :: 
    0 <= i < j < a.Length ==>
      a[i] <= a[j]
}
// pure-end

function inversions(a: array<T>): set<(nat, nat)>
  reads a
{
  set i, j | 0 <= i < j < a.Length && a[i] > a[j] :: (i, j)
}
// pure-end

method rawsort(a: array<T>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies a
  ensures sorted(a) && multiset(a[..]) == multiset(old(a[..]))
  decreases |inversions(a)|
  // post-conditions-end
{
// impl-start
  if i, j :| 0 <= i < j < a.Length && a[i] > a[j] {
    ghost var bef := inversions(a);
    a[i], a[j] := a[j], a[i];
    ghost var aft := inversions(a);
    ghost var aft2bef := map p | p in aft :: (if p.0 == i && p.1 > j then j else if p.0 == j then i else p.0, if p.1 == i then j else if p.1 == j && p.0 < i then i else p.1);
    // assert-start
    mappingProp(aft, bef, (i, j), aft2bef);
    // assert-end

    rawsort(a);
  }
// impl-end
}

lemma mappingProp<T1, T2>(a: set<T1>, b: set<T2>, k: T2, m: map<T1, T2>)
  // pre-conditions-start
  requires k in b
  requires forall x :: x in a ==> x in m && m[x] in b - {k}
  requires forall x, y :: x in a && y in a && x != y ==> m[x] != m[y]
  // pre-conditions-end
  // post-conditions-start
  ensures |a| < |b|
  // post-conditions-end
{
// impl-start
  if x :| x in a {
    mappingProp(a - {x}, b - {m[x]}, k, m);
  }
// impl-end
}

method testRawsort()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a: array<T> := new T[] [3, 5, 1];
  // assert-start
  assert a[..] == [3, 5, 1];
  // assert-end

  rawsort(a);
  // assert-start
  assert a[..] == [1, 3, 5];
  // assert-end

// impl-end
}

type T = int
