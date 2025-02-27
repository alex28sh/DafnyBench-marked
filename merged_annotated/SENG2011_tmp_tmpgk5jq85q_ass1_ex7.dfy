method BigFoot(step: nat)
  // pre-conditions-start
  requires 0 < step <= 42
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var indx := 0;
  while indx <= 42
    // invariants-start

    invariant 0 <= indx <= step + 42 && indx % step == 0
    decreases 42 - indx
    // invariants-end

  {
    indx := indx + step;
  }
  // assert-start
  assert 0 <= indx <= step + 42 && indx % step == 0 && indx > 42;
  // assert-end

// impl-end
}
