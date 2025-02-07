function quickSorted(Seq: seq<int>): bool
{
  forall idx_1, idx_2 :: 
    0 <= idx_1 < idx_2 < |Seq| ==>
      Seq[idx_1] <= Seq[idx_2]
}
// pure-end

method threshold(thres: int, Seq: seq<int>)
    returns (Seq_1: seq<int>, Seq_2: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures (forall x | x in Seq_1 :: x <= thres) && forall x | x in Seq_2 :: x >= thres
  ensures |Seq_1| + |Seq_2| == |Seq|
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
  // post-conditions-end
{
// impl-start
  Seq_1 := [];
  Seq_2 := [];
  var i := 0;
  while i < |Seq|
    // invariants-start

    invariant i <= |Seq|
    invariant (forall x | x in Seq_1 :: x <= thres) && forall x | x in Seq_2 :: x >= thres
    invariant |Seq_1| + |Seq_2| == i
    invariant multiset(Seq[..i]) == multiset(Seq_1) + multiset(Seq_2)
    // invariants-end

  {
    if Seq[i] <= thres {
      Seq_1 := Seq_1 + [Seq[i]];
    } else {
      Seq_2 := Seq_2 + [Seq[i]];
    }
    // assert-start
    assert Seq[..i] + [Seq[i]] == Seq[..i + 1];
    // assert-end

    i := i + 1;
  }
  // assert-start
  assert Seq[..|Seq|] == Seq;
  // assert-end

// impl-end
}

lemma Lemma_1(Seq_1: seq, Seq_2: seq)
  // pre-conditions-start
  requires multiset(Seq_1) == multiset(Seq_2)
  // pre-conditions-end
  // post-conditions-start
  ensures forall x | x in Seq_1 :: x in Seq_2
  // post-conditions-end
{
// impl-start
  forall x | x in Seq_1
    ensures x in multiset(Seq_1)
  {
    var i := 0;
    while i < |Seq_1|
      invariant 0 <= i <= |Seq_1|
      invariant forall idx_1 | 0 <= idx_1 < i :: Seq_1[idx_1] in multiset(Seq_1)
    {
      i := i + 1;
    }
  }
// impl-end
}

method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures multiset(Seq) == multiset(Seq')
  decreases |Seq|
  // post-conditions-end
{
// impl-start
  if |Seq| == 0 {
    return [];
  } else if |Seq| == 1 {
    return Seq;
  } else {
    var Seq_1, Seq_2 := threshold(Seq[0], Seq[1..]);
    var Seq_1' := quickSort(Seq_1);
    // assert-start
    Lemma_1(Seq_1', Seq_1);
    // assert-end

    var Seq_2' := quickSort(Seq_2);
    // assert-start
    Lemma_1(Seq_2', Seq_2);
    // assert-end

    // assert-start
    assert Seq == [Seq[0]] + Seq[1..];
    // assert-end

    return Seq_1' + [Seq[0]] + Seq_2';
  }
// impl-end
}
