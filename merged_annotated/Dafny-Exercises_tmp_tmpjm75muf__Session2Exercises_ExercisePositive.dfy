function positive(s: seq<int>): bool
{
  forall u :: 
    0 <= u < |s| ==>
      s[u] >= 0
}
// pure-end

method mpositive(v: array<int>) returns (b: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures b == positive(v[0 .. v.Length])
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < v.Length && v[i] >= 0
    // invariants-start

    invariant 0 <= i <= v.Length
    invariant positive(v[..i])
    decreases v.Length - i
    // invariants-end

  {
    i := i + 1;
  }
  b := i == v.Length;
// impl-end
}

method mpositive3(v: array<int>) returns (b: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures b == positive(v[0 .. v.Length])
  // post-conditions-end
{
// impl-start
  var i := 0;
  b := true;
  while i < v.Length && b
    // invariants-start

    invariant 0 <= i <= v.Length
    invariant b == positive(v[0 .. i])
    invariant !b ==> !positive(v[0 .. v.Length])
    decreases v.Length - i
    // invariants-end

  {
    b := v[i] >= 0;
    i := i + 1;
  }
// impl-end
}

method mpositive4(v: array<int>) returns (b: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures b == positive(v[0 .. v.Length])
  // post-conditions-end
{
// impl-start
  var i := 0;
  b := true;
  while i < v.Length && b
    // invariants-start

    invariant 0 <= i <= v.Length
    invariant b == positive(v[0 .. i])
    invariant !b ==> !positive(v[0 .. v.Length])
    decreases v.Length - i
    // invariants-end

  {
    b := v[i] >= 0;
    i := i + 1;
  }
// impl-end
}

method mpositivertl(v: array<int>) returns (b: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures b == positive(v[0 .. v.Length])
  // post-conditions-end
{
// impl-start
  var i := v.Length - 1;
  while i >= 0 && v[i] >= 0
    // invariants-start

    invariant -1 <= i < v.Length
    invariant positive(v[i + 1..])
    decreases i
    // invariants-end

  {
    i := i - 1;
  }
  b := i == -1;
// impl-end
}
