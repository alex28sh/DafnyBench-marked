method Maximum(values: seq<int>) returns (max: int)
  // pre-conditions-start
  requires values != []
  // pre-conditions-end
  // post-conditions-start
  ensures max in values
  ensures forall i | 0 <= i < |values| :: values[i] <= max
  // post-conditions-end
{
// impl-start
  max := values[0];
  var idx := 0;
  while idx < |values|
    // invariants-start

    invariant max in values
    invariant idx <= |values|
    invariant forall j | 0 <= j < idx :: values[j] <= max
    // invariants-end

  {
    if values[idx] > max {
      max := values[idx];
    }
    idx := idx + 1;
  }
// impl-end
}

lemma MaximumIsUnique(values: seq<int>, m1: int, m2: int)
  // pre-conditions-start
  requires m1 in values && forall i | 0 <= i < |values| :: values[i] <= m1
  requires m2 in values && forall i | 0 <= i < |values| :: values[i] <= m2
  // pre-conditions-end
  // post-conditions-start
  ensures m1 == m2
  // post-conditions-end
{
// impl-start
// impl-end
}
