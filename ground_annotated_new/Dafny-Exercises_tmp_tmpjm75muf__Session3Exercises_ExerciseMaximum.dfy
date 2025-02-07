method mmaximum1(v: array<int>) returns (i: int)
  // pre-conditions-start
  requires v.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= i < v.Length
  ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
  // post-conditions-end
{
// impl-start
  var j := 1;
  i := 0;
  while j < v.Length
    // invariants-start

    invariant 0 <= j <= v.Length
    invariant 0 <= i < j
    invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
    decreases v.Length - j
    // invariants-end

  {
    if v[j] > v[i] {
      i := j;
    }
    j := j + 1;
  }
// impl-end
}

method mmaximum2(v: array<int>) returns (i: int)
  // pre-conditions-start
  requires v.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= i < v.Length
  ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
  // post-conditions-end
{
// impl-start
  var j := v.Length - 2;
  i := v.Length - 1;
  while j >= 0
    // invariants-start

    invariant 0 <= i < v.Length
    invariant -1 <= j < v.Length - 1
    invariant forall k :: v.Length > k > j ==> v[k] <= v[i]
    decreases j
    // invariants-end

  {
    if v[j] > v[i] {
      i := j;
    }
    j := j - 1;
  }
// impl-end
}

method mfirstMaximum(v: array<int>) returns (i: int)
  // pre-conditions-start
  requires v.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= i < v.Length
  ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
  ensures forall l :: 0 <= l < i ==> v[i] > v[l]
  // post-conditions-end
{
// impl-start
  var j := 1;
  i := 0;
  while j < v.Length
    // invariants-start

    invariant 0 <= j <= v.Length
    invariant 0 <= i < j
    invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
    invariant forall k :: 0 <= k < i ==> v[i] > v[k]
    decreases v.Length - j
    // invariants-end

  {
    if v[j] > v[i] {
      i := j;
    }
    j := j + 1;
  }
// impl-end
}

method mlastMaximum(v: array<int>) returns (i: int)
  // pre-conditions-start
  requires v.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= i < v.Length
  ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
  ensures forall l :: i < l < v.Length ==> v[i] > v[l]
  // post-conditions-end
{
// impl-start
  var j := v.Length - 2;
  i := v.Length - 1;
  while j >= 0
    // invariants-start

    invariant -1 <= j < v.Length - 1
    invariant 0 <= i < v.Length
    invariant forall k :: v.Length > k > j ==> v[k] <= v[i]
    invariant forall k :: v.Length > k > i ==> v[k] < v[i]
    decreases j
    // invariants-end

  {
    if v[j] > v[i] {
      i := j;
    }
    j := j - 1;
  }
// impl-end
}

method mmaxvalue1(v: array<int>) returns (m: int)
  // pre-conditions-start
  requires v.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures m in v[..]
  ensures forall k :: 0 <= k < v.Length ==> m >= v[k]
  // post-conditions-end
{
// impl-start
  var i := mmaximum1(v);
  m := v[i];
// impl-end
}

method mmaxvalue2(v: array<int>) returns (m: int)
  // pre-conditions-start
  requires v.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures m in v[..]
  ensures forall k :: 0 <= k < v.Length ==> m >= v[k]
  // post-conditions-end
{
// impl-start
  var i := mmaximum2(v);
  m := v[i];
// impl-end
}
