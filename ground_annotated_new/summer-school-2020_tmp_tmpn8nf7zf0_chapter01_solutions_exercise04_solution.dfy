function AtLeastTwiceAsBigFunction(a: int, b: int): bool
{
  a >= 2 * b
}
// pure-end

function AtLeastTwiceAsBigPredicate(a: int, b: int): bool
{
  a >= 2 * b
}
// pure-end

function Double(a: int): int
{
  2 * a
}
// pure-end

lemma TheseTwoPredicatesAreEquivalent(x: int, y: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  assert AtLeastTwiceAsBigFunction(x, y) == AtLeastTwiceAsBigPredicate(x, y);
// impl-end
}

lemma FourTimesIsPrettyBig(x: int)
  // pre-conditions-start
  requires x >= 0
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  assert AtLeastTwiceAsBigPredicate(Double(Double(x)), x);
// impl-end
}
