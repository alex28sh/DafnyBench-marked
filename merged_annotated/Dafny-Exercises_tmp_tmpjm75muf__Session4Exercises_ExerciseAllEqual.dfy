function allEqual(s: seq<int>): bool
{
  forall i, j :: 
    0 <= i < |s| &&
    0 <= j < |s| ==>
      s[i] == s[j]
}
// pure-end

lemma equivalenceNoOrder(s: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures allEqual(s) <==> forall i, j :: 0 <= i <= j < |s| ==> s[i] == s[j]
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma equivalenceEqualtoFirst(s: seq<int>)
  // pre-conditions-start
  requires s != []
  // pre-conditions-end
  // post-conditions-start
  ensures allEqual(s) <==> forall i :: 0 <= i < |s| ==> s[0] == s[i]
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma equivalenceContiguous(s: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures allEqual(s) ==> forall i :: 0 <= i < |s| - 1 ==> s[i] == s[i + 1]
  ensures allEqual(s) <== forall i :: 0 <= i < |s| - 1 ==> s[i] == s[i + 1]
  // post-conditions-end
{
// impl-start
  assert allEqual(s) ==> forall i :: 0 <= i < |s| - 1 ==> s[i] == s[i + 1];
  if |s| == 0 || |s| == 1 {
  } else {
    calc {
      forall i :: 
        0 <= i < |s| - 1 ==>
          s[i] == s[i + 1];
    ==>
      {
        equivalenceContiguous(s[..|s| - 1]);
        assert s[|s| - 2] == s[|s| - 1];
      }
      allEqual(s);
    }
  }
// impl-end
}

method mallEqual1(v: array<int>) returns (b: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures b == allEqual(v[0 .. v.Length])
  // post-conditions-end
{
// impl-start
  var i := 0;
  b := true;
  while i < v.Length && b
    // invariants-start

    invariant 0 <= i <= v.Length
    invariant b == allEqual(v[..i])
    decreases v.Length - i
    // invariants-end

  {
    b := v[i] == v[0];
    i := i + 1;
  }
// impl-end
}

method mallEqual2(v: array<int>) returns (b: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures b == allEqual(v[0 .. v.Length])
  // post-conditions-end
{
// impl-start
  var i: int;
  b := true;
  i := 0;
  while i < v.Length && v[i] == v[0]
    // invariants-start

    invariant 0 <= i <= v.Length
    invariant forall k :: 0 <= k < i ==> v[k] == v[0]
    decreases v.Length - i
    // invariants-end

  {
    i := i + 1;
  }
  b := i == v.Length;
// impl-end
}

method mallEqual3(v: array<int>) returns (b: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures b == allEqual(v[0 .. v.Length])
  // post-conditions-end
{
// impl-start
  // assert-start
  equivalenceContiguous(v[..]);
  // assert-end

  var i: int;
  b := true;
  if v.Length > 0 {
    i := 0;
    while i < v.Length - 1 && v[i] == v[i + 1]
      // invariants-start

      invariant 0 <= i <= v.Length - 1
      invariant b == allEqual(v[..i + 1])
      decreases v.Length - i
      // invariants-end

    {
      i := i + 1;
    }
    b := i == v.Length - 1;
  }
// impl-end
}

method mallEqual4(v: array<int>) returns (b: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures b == allEqual(v[0 .. v.Length])
  // post-conditions-end
{
// impl-start
  var i: int;
  b := true;
  if v.Length > 0 {
    i := 0;
    while i < v.Length - 1 && b
      // invariants-start

      invariant 0 <= i < v.Length
      invariant b == allEqual(v[..i + 1])
      decreases v.Length - i
      // invariants-end

    {
      b := v[i] == v[i + 1];
      i := i + 1;
    }
  }
// impl-end
}

method mallEqual5(v: array<int>) returns (b: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures b == allEqual(v[0 .. v.Length])
  // post-conditions-end
{
// impl-start
  var i := 0;
  b := true;
  while i < v.Length && b
    // invariants-start

    invariant 0 <= i <= v.Length
    invariant b ==> forall k :: 0 <= k < i ==> v[k] == v[0]
    invariant !b ==> exists k :: 0 <= k < v.Length && v[k] != v[0]
    decreases v.Length - i - if b then 0 else 1
    // invariants-end

  {
    if v[i] != v[0] {
      b := false;
    } else {
      i := i + 1;
    }
  }
// impl-end
}
