lemma TestMap(a: map<int, (int, int)>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  assert (map k | k in a :: k := a[k].0) == map k | k in a :: a[k].0;
// impl-end
}

lemma TestSet0(a: set<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  assert (set k | k in a && k < 7 :: k) == set k | k in a && k < 7;
// impl-end
}

lemma TestSet1(a: set<int>, m: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  assert (set k | k in a && k < 7 :: k) == set k | k in a && k < 7 :: m + (k - m);
// impl-end
}

lemma TestSet2(a: set<int>, m: int)
  // pre-conditions-start
  requires m in a && m < 7
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  assert (set k | k < 7 && k in a) == set k | k in a :: if k < 7 then k else m;
// impl-end
}
