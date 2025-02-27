lemma SeqRank0(a: Abc)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a != Wrapper([a])
  // post-conditions-end
{
// impl-start
  assert [a][0] == a;
// impl-end
}

lemma SeqRank1(s: seq<Abc>)
  // pre-conditions-start
  requires s != []
  // pre-conditions-end
  // post-conditions-start
  ensures s[0] != Wrapper(s)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma MultisetRank(a: Def)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a != MultiWrapper(multiset{a})
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma SetRank(a: Ghi)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a != SetWrapper({a})
  // post-conditions-end
{
// impl-start
// impl-end
}

datatype Abc = End | Wrapper(seq<Abc>)

datatype Def = End | MultiWrapper(multiset<Def>)

datatype Ghi = End | SetWrapper(set<Ghi>)
