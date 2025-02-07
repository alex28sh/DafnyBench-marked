method Filter(a: seq<char>, b: set<char>) returns (c: set<char>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures forall x :: x in a && x in b <==> x in c
  // post-conditions-end
{
// impl-start
  var setA: set<char> := set x | x in a;
  c := setA * b;
// impl-end
}

method TesterFilter()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var v: set<char> := {'a', 'e', 'i', 'o', 'u'};
  var s: seq<char> := "ant-egg-ink-owl-urn";
  var w: set<char> := Filter(s, v);
  // assert-start
  assert w == {'i', 'u', 'a', 'o', 'e'};
  // assert-end

  s := "nice-and-easy";
  w := Filter(s, v);
  // assert-start
  assert w == {'a', 'e', 'i'};
  // assert-end

  s := "mssyysywbrpqsxmnlsghrytx";
  w := Filter(s, v);
  // assert-start
  assert w == {};
  // assert-end

  s := "iiiiiiiiiiiii";
  w := Filter(s, v);
  // assert-start
  assert w == {'i'};
  // assert-end

  s := "aeiou";
  w := Filter(s, v);
  // assert-start
  assert w == {'a', 'e', 'i', 'o', 'u'};
  // assert-end

  s := "u";
  w := Filter(s, v);
  // assert-start
  assert w == {'u'};
  // assert-end

  s := "f";
  w := Filter(s, v);
  // assert-start
  assert w == {};
  // assert-end

  s := "";
  w := Filter(s, v);
  // assert-start
  assert w == {};
  // assert-end

  v := {};
  s := "Any sequence that I like!!!";
  w := Filter(s, v);
  // assert-start
  assert w == {};
  // assert-end

// impl-end
}
