method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
  // pre-conditions-start
  requires A < B
  // pre-conditions-end
  // post-conditions-start
  ensures |A| < |B|
  decreases B
  // post-conditions-end
{
// impl-start
  var b :| b in B && b !in A;
  var B' := B - {b};
  // assert-start
  assert |B| == |B'| + 1;
  // assert-end

  if A < B' {
    CardinalitySubsetLt(A, B');
  } else {
    // assert-start
    assert A == B';
    // assert-end

  }
// impl-end
}

method strategy<T>(P: set<T>, Special: T) returns (count: int)
  // pre-conditions-start
  requires |P| > 1 && Special in P
  // pre-conditions-end
  // post-conditions-start
  ensures count == |P| - 1
  decreases *
  // post-conditions-end
{
// impl-start
  count := 0;
  var I := {};
  var S := {};
  var switch := false;
  while count < |P| - 1
    // invariants-start

    invariant count <= |P| - 1
    invariant count > 0 ==> Special in I
    invariant Special !in S && S < P && S <= I <= P
    invariant if switch then |S| == count + 1 else |S| == count
    decreases *
    // invariants-end

  {
    var p :| p in P;
    I := I + {p};
    if p == Special {
      if switch {
        switch := false;
        count := count + 1;
      }
    } else {
      if p !in S && !switch {
        S := S + {p};
        switch := true;
      }
    }
  }
  CardinalitySubsetLt(S, I);
  if I < P {
    CardinalitySubsetLt(I, P);
  }
  // assert-start
  assert P <= I;
  // assert-end

  // assert-start
  assert I == P;
  // assert-end

// impl-end
}
