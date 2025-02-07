function Average(a: int, b: int): int
{
  (a + b) / 2
}
// pure-end

method TripleConditions(x: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r == 3 * x
  // post-conditions-end
{
// impl-start
  r := 3 * x;
  // assert-start
  assert r == 3 * x;
  // assert-end

// impl-end
}

method Triple'(x: int) returns (r: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Average(r, 3 * x) == 3 * x
  ensures r == 3 * x
  // post-conditions-end
{
// impl-start
  r := 3 * x;
// impl-end
}

method ProveSpecificationsEquivalent(x: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var result1 := TripleConditions(x);
  var result2 := Triple'(x);
  // assert-start
  assert result1 == result2;
  // assert-end

// impl-end
}
