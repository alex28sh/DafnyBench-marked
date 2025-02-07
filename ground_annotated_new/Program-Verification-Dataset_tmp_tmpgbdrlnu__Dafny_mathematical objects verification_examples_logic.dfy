lemma ExampleProposition()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  assert 2 < 3;
// impl-end
}

lemma SomethingFalse()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma SomethingNonsensical()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma AdditionCommutes(n: int, m: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures n + m == m + n
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma ProveAndFromBoth(p1: bool, p2: bool)
  // pre-conditions-start
  requires p1
  requires p2
  // pre-conditions-end
  // post-conditions-start
  ensures p1 && p2
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma FromAndProveRight(p1: bool, p2: bool)
  // pre-conditions-start
  requires p1 && p2
  // pre-conditions-end
  // post-conditions-start
  ensures p2
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma ProveOrFromLeft(p1: bool, p2: bool)
  // pre-conditions-start
  requires p1
  // pre-conditions-end
  // post-conditions-start
  ensures p1 || p2
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma DoubleNegation(p: bool)
  // pre-conditions-start
  requires p
  // pre-conditions-end
  // post-conditions-start
  ensures !!p
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma LawOfExcludedMiddle(p: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures p || !p
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma ImplicationTruthTable()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures false ==> false
  ensures false ==> true
  ensures !(true ==> false)
  ensures false ==> true
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma ModusPonens(p1: bool, p2: bool)
  // pre-conditions-start
  requires p1 ==> p2
  requires p1
  // pre-conditions-end
  // post-conditions-start
  ensures p2
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma AndProvesBoth(p1: bool, p2: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures p1 && p2 ==> p1
  ensures p1 && p2 ==> p2
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma ProveFromBiconditional(p1: bool, p2: bool)
  // pre-conditions-start
  requires p1
  requires p1 <==> p2
  // pre-conditions-end
  // post-conditions-start
  ensures p2
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma SomeEquivalences(p1: bool, p2: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures (p1 ==> p2) && p1 ==> p2
  ensures p1 ==> p2 <==> !p2 ==> !p1
  ensures !(p1 ==> !p2) <==> p1 && p2
  ensures (p1 ==> p2) && (!p1 ==> p2) <==> p2
  ensures !p1 || (p1 ==> p2) <==> p1 ==> p2
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma SomeMoreEquivalences(p1: bool, p2: bool, p3: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures p1 && p2 && p3 <==> p1 && p2 && p3
  ensures p1 ==> p2 ==> p3 <==> p1 && p2 ==> p3
  ensures p1 ==> p2 ==> p3 <==> p1 && p2 ==> p3
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma AdditionCommutesAsForall()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  assert forall n: int, m: int :: n + m == m + n;
  var does_addition_commute: bool := forall n: int, m: int :: n + m == m + n;
  assert does_addition_commute == true;
// impl-end
}

function P(x: int): bool
// pure-end

function Q(x: int): bool
// pure-end

function R(x: int, y: int): bool
// pure-end

lemma SimplifyingNegations(p: bool, q: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures !(p && q) <==> !p || !q
  ensures !(p || q) <==> !p && !q
  ensures !(p ==> q) <==> p && !q
  ensures !!p <==> p
  ensures !(forall x :: P(x)) <==> exists x :: !P(x)
  ensures !(exists x :: P(x)) <==> forall x :: !P(x)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma WhereIsJustImplies()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures (forall x | P(x) :: Q(x)) <==> forall x :: P(x) ==> Q(x)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma NotForallWhere()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures !(forall x | P(x) :: Q(x)) <==> exists x :: P(x) && !Q(x)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma ExistsWhereIsJustAnd()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures (exists x | P(x) :: Q(x)) <==> exists x :: P(x) && Q(x)
  ensures !(forall x | P(x) :: Q(x)) <==> exists x | P(x) :: !Q(x)
  // post-conditions-end
{
// impl-start
// impl-end
}
