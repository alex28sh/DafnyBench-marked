method MaxLengthList(lists: seq<seq<int>>) returns (maxList: seq<int>)
  // pre-conditions-start
  requires |lists| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall l :: l in lists ==> |l| <= |maxList|
  ensures maxList in lists
  // post-conditions-end
{
// impl-start
  maxList := lists[0];
  for i := 1 to |lists|
    // invariants-start

    invariant 1 <= i <= |lists|
    invariant forall l :: l in lists[..i] ==> |l| <= |maxList|
    invariant maxList in lists[..i]
    // invariants-end

  {
    if |lists[i]| > |maxList| {
      maxList := lists[i];
    }
  }
// impl-end
}
