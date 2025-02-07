lemma Q1_logical_equivalence_as_a_conjunction_of_two_implications__PROOF_BY_TRUTH_TABLE__in_a_comment(L: bool, R: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures L <==> R <==> (L ==> R) && (!L ==> !R)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma Q2_DistributivityOfSetUnionOverSetIntersection(A: set, B: set, C: set)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures A + B * C == (A + B) * (A + C)
  // post-conditions-end
{
// impl-start
  var L,R := (A + B) + C, A + (B + C);
  forall x | x in L ensures x in R
  {
    assert 1: x in (A + B) + C;
    assert 2: (x in  A || x in B) || x in C by {reveal 1; }
    assert 3: x in A || (x in B || x in C) by {reveal 2; }
    assert 4: x in A + (B + C) by {reveal 3; }
    assert 5: x in R by {reveal 4; }

  }

    forall x | x in R ensures x in L
  {
    assert 6: x in A + (B + C);
    assert 7: x in A || (x in B || x in C ) by {reveal 6; }
    assert 8: (x in A|| x in B) || x in C by {reveal 7; }
    assert 9: x in (A + B) + C by {reveal 8; }
    assert 10: x in L by {reveal 9; }
  }
// impl-end
}

lemma Q3_SetUnionIsAssociative(A: iset, B: iset, C: iset)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures A + B + C == A + (B + C)
  // post-conditions-end
{
// impl-start
  var L, R := A + B + C, A + (B + C);
  forall x | x in L
    ensures x in R
  {
    assert 1: x in A + B + C;
    assert 2: x in A || x in B || x in C by {
      reveal 1;
    }
    assert 3: x in A || x in B || x in C by {
      reveal 2;
    }
    assert 4: x in A + (B + C) by {
      reveal 3;
    }
    assert 5: x in R by {
      reveal 4;
    }
  }
  forall x | x in R
    ensures x in L
  {
    assert 6: x in A + (B + C);
    assert 7: x in A || x in B || x in C by {
      reveal 6;
    }
    assert 8: x in A || x in B || x in C by {
      reveal 7;
    }
    assert 9: x in A + B + C by {
      reveal 8;
    }
    assert 10: x in L by {
      reveal 9;
    }
  }
// impl-end
}

lemma preparation_for_Q4_SetDifferenceIs_NOT_Associative()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures !forall A: set<int>, B: set<int>, C: set<int> :: A - B - C == A - (B - C)
  // post-conditions-end
{
// impl-start
  assert exists A: set<int>, B: set<int>, C: set<int> :: A - B - C != A - (B - C) by {
    var A, B, C := Q4_Evidence_That_SetDifferenceIs_NOT_Associative();
    assert A - B - C != A - (B - C);
  }
// impl-end
}

lemma Q4_Evidence_That_SetDifferenceIs_NOT_Associative() returns (A: set<int>, B: set<int>, C: set<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures A - B - C != A - (B - C)
  // post-conditions-end
{
// impl-start
  A := {6, 3, 7};
  B := {1, 6};
  C := {3, 2, 5};
  assert A - B - C != A - (B - C);
  calc {
    A - B - C != A - (B - C);
  ==
    ({6, 3, 7} - {1, 6} - {3, 2, 5}) != ({6, 3, 7} - ({1, 6} - {3, 2, 5}));
  ==
    ({7} != {3, 7});
  ==
    true;
  }
// impl-end
}
