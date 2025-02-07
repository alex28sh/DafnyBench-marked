function IsSubset(A: set, B: set): bool
{
  forall n :: 
    n in A ==>
      n in B
}
// pure-end

lemma subsetIsTransitive(A: set, B: set, C: set)
  // pre-conditions-start
  requires Pre1: IsSubset(A, B)
  requires Pre2: IsSubset(B, C)
  // pre-conditions-end
  // post-conditions-start
  ensures IsSubset(A, C)
  // post-conditions-end
{
// impl-start
  forall x | x in A
    ensures x in C
  {
    assert 3: x in A;
    assert 4: x in B by {
      reveal 3, Pre1;
    }
    assert x in C by {
      reveal 4, Pre2;
    }
  }
// impl-end
}
