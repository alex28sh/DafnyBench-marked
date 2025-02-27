function ContainsNothingBut5(s: set<int>): bool
{
  forall q :: 
    q in s ==>
      q == 5
}
// pure-end

function YeahContains5(s: set<int>): bool
{
  exists q :: 
    q in s &&
    q == 5
}
// pure-end

function ViaSetComprehension(s: set<int>): bool
{
  |set q | q in s && q == 5| != 0
}
// pure-end

function LambdaTest(s: set<int>): bool
{
  (q => q in s)(5)
}
// pure-end

function ViaMapComprehension(s: set<int>): bool
{
  |(map q | q in s && q == 5 :: true).Keys| != 0
}
// pure-end

function Contains5(s: set<int>): bool
{
  var q := 5;
  q in s
}
// pure-end

function RIs5(r: R): bool
{
  match r
  case MakeR(q) =>
    q == 5
  case Other =>
    false
}
// pure-end

lemma NonemptySet(x: int, s: set<int>)
  // pre-conditions-start
  requires x in s
  // pre-conditions-end
  // post-conditions-start
  ensures |s| != 0
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma NonemptyMap(x: int, s: map<int, bool>)
  // pre-conditions-start
  requires x in s.Keys
  // pre-conditions-end
  // post-conditions-start
  ensures |s| != 0
  // post-conditions-end
{
// impl-start
// impl-end
}

method M(s: set<int>, r: R, q: int)
  // pre-conditions-start
  requires s == {5} && r == MakeR(5)
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert ContainsNothingBut5(s);
  // assert-end

  // assert-start
  assert YeahContains5(s);
  // assert-end

  // assert-start
  NonemptySet(5, set q | q in s && q == 5);
  // assert-end

  // assert-start
  assert ViaSetComprehension(s);
  // assert-end

  // assert-start
  NonemptyMap(5, map q | q in s && q == 5 :: true);
  // assert-end

  // assert-start
  assert ViaMapComprehension(s);
  // assert-end

  // assert-start
  assert LambdaTest(s);
  // assert-end

  // assert-start
  assert Contains5(s);
  // assert-end

  // assert-start
  assert RIs5(r);
  // assert-end

// impl-end
}

datatype R = MakeR(int) | Other
