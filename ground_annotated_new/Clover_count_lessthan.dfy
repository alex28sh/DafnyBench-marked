method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures count == |set i | i in numbers && i < threshold|
  // post-conditions-end
{
// impl-start
  count := 0;
  var shrink := numbers;
  var grow := {};
  while |shrink| > 0
    // invariants-start

    invariant shrink + grow == numbers
    invariant grow !! shrink
    invariant count == |set i | i in grow && i < threshold|
    decreases shrink
    // invariants-end

  {
    var i: int :| i in shrink;
    shrink := shrink - {i};
    var grow' := grow + {i};
    // assert-start
    assert (set i | i in grow' && i < threshold) == (set i | i in grow && i < threshold) + if i < threshold then {i} else {};
    // assert-end

    grow := grow + {i};
    if i < threshold {
      count := count + 1;
    }
  }
// impl-end
}
