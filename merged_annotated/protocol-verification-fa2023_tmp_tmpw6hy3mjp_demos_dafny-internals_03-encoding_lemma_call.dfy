function f(x: int): int
// pure-end

lemma {:axiom} f_positive(x: int)
  // pre-conditions-start
  requires x >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures f(x) >= 0
  // post-conditions-end

lemma f_2_pos()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures f(2) >= 0
  // post-conditions-end
{
// impl-start
  f_positive(2);
// impl-end
}

lemma f_1_1_pos()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures f(1 + 1) >= 0
  // post-conditions-end
{
// impl-start
  f_2_pos();
  assert 1 + 1 == 2;
// impl-end
}
