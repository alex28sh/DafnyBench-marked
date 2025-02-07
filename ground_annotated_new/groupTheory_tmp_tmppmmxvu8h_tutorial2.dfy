ghost method M1()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  assert 1 != 3;
  assume 1 == 2;
  assert 1 == 2;
// impl-end
}

lemma IntersectionIsSubsetOfBoth(A: set, B: set, C: set)
  // pre-conditions-start
  requires C == A * B
  // pre-conditions-end
  // post-conditions-start
  ensures C <= A && C <= B
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma BothSetsAreSubsetsOfTheirUnion(A: set, B: set, C: set)
  // pre-conditions-start
  requires C == A + B
  // pre-conditions-end
  // post-conditions-start
  ensures A <= C && B <= C
  // post-conditions-end
{
// impl-start
// impl-end
}

const s0 := {3, 8, 1}

lemma M2()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var s1 := {2, 4, 6, 8};
  assert |s1| == 4;
  s1 := {};
  assert |s1| == 0;
  assert s1 <= s0;
// impl-end
}

lemma TheEmptySetIsASubsetOfAnySet(A: set, B: set)
  // pre-conditions-start
  requires A == {}
  // pre-conditions-end
  // post-conditions-start
  ensures A <= B
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma AnySetIsASubsetOfItself(A: set)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures A <= A
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma TheIntersectionOfTwoSetsIsASubsetOfTheirUnion(A: set, B: set, C: set, D: set)
  // pre-conditions-start
  requires C == A * B && D == A + B
  // pre-conditions-end
  // post-conditions-start
  ensures C <= D
  // post-conditions-end
{
// impl-start
  assert C <= A by {
    assert C == A * B;
    IntersectionIsSubsetOfBoth(A, B, C);
  }
  assert A <= D by {
    assert D == A + B;
    BothSetsAreSubsetsOfTheirUnion(A, B, D);
  }
// impl-end
}
