method toMultiset(s: string) returns (mset: multiset<char>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures multiset(s) == mset
  // post-conditions-end
{
// impl-start
  mset := multiset{};
  for i := 0 to |s|
    // invariants-start

    invariant mset == multiset(s[0 .. i])
    // invariants-end

  {
    // assert-start
    assert s == s[0 .. i] + [s[i]] + s[i + 1..];
    // assert-end

    mset := mset + multiset{s[i]};
  }
  // assert-start
  assert s == s[0 .. |s|];
  // assert-end

  return mset;
// impl-end
}

method msetEqual(s: multiset<char>, t: multiset<char>) returns (equal: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures s == t <==> equal
  // post-conditions-end
{
// impl-start
  ghost var sremoved: multiset<char> := multiset{};
  var scopy := s;
  while scopy != multiset{}
    // invariants-start

    invariant s - sremoved == scopy
    invariant sremoved !! scopy
    invariant sremoved <= s
    invariant forall x :: x in sremoved ==> x in s && x in t && t[x] == s[x]
    // invariants-end

  {
    var x :| x in scopy;
    if !(x in t && s[x] == t[x]) {
      return false;
    }
    var removed := multiset{};
    sremoved := sremoved + removed[x := s[x]];
    scopy := scopy - removed[x := s[x]];
  }
  ghost var tremoved: multiset<char> := multiset{};
  var tcopy := t;
  while tcopy != multiset{}
    // invariants-start

    invariant t - tremoved == tcopy
    invariant tremoved !! tcopy
    invariant tremoved <= t
    invariant forall x :: x in tremoved ==> x in s && x in t && t[x] == s[x]
    // invariants-end

  {
    var x :| x in tcopy;
    if !(x in t && s[x] == t[x]) {
      return false;
    }
    var removed := multiset{};
    tremoved := tremoved + removed[x := s[x]];
    tcopy := tcopy - removed[x := s[x]];
  }
  return true;
// impl-end
}

method isAnagram(s: string, t: string) returns (equal: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures (multiset(s) == multiset(t)) == equal
  // post-conditions-end
{
// impl-start
  var smset := toMultiset(s);
  var tmset := toMultiset(t);
  equal := msetEqual(smset, tmset);
// impl-end
}
