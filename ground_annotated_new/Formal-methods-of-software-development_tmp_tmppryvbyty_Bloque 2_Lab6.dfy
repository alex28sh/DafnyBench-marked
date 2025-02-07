function sum(v: seq<int>): int
  decreases v
{
  if v == [] then
    0
  else if |v| == 1 then
    v[0]
  else
    v[0] + sum(v[1..])
}
// pure-end

lemma empty_Lemma<T>(r: seq<T>)
  // pre-conditions-start
  requires multiset(r) == multiset{}
  // pre-conditions-end
  // post-conditions-start
  ensures r == []
  // post-conditions-end
{
// impl-start
  if r != [] {
    assert r[0] in multiset(r);
  }
// impl-end
}

lemma elem_Lemma<T>(s: seq<T>, r: seq<T>)
  // pre-conditions-start
  requires s != [] && multiset(s) == multiset(r)
  // pre-conditions-end
  // post-conditions-start
  ensures exists i :: 0 <= i < |r| && r[i] == s[0] && multiset(s[1..]) == multiset(r[..i] + r[i + 1..])
  // post-conditions-end

lemma sumElems_Lemma(s: seq<int>, r: seq<int>)
  // pre-conditions-start
  requires multiset(s) == multiset(r)
  // pre-conditions-end
  // post-conditions-start
  ensures sum(s) == sum(r)
  // post-conditions-end
{
// impl-start
  if s == [] {
    empty_Lemma(r);
  } else {
    elem_Lemma(s, r);
    var i :| 0 <= i < |r| && r[i] == s[0] && multiset(s[1..]) == multiset(r[..i] + r[i + 1..]);
    sumElems_Lemma(s[1..], r[..i] + r[i + 1..]);
    assert sum(s[1..]) == sum(r[..i] + r[i + 1..]);
    sumElems_Lemma(s[1..], r[..i] + r[i + 1..]);
    assert sum(s[1..]) == sum(r[..i] + r[i + 1..]);
    calc {
      sum(s);
      s[0] + sum(s[1..]);
      {
        sumElems_Lemma(s[1..], r[..i] + r[i + 1..]);
        assert sum(s[1..]) == sum(r[..i] + r[i + 1..]);
      }
      s[0] + sum(r[..i] + r[i + 1..]);
      {
        assert s[0] == r[i];
      }
      r[i] + sum(r[..i] + r[i + 1..]);
      {
        assume r[i] + sum(r[..i] + r[i + 1..]) == sum([r[i]] + r[..i] + r[i + 1..]) == sum(r);
      }
      sum(r);
    }
  }
// impl-end
}
