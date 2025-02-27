lemma SkippingLemma(a: array<int>, j: int)
  // pre-conditions-start
  requires a != null
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i - 1] - 1 <= a[i]
  requires 0 <= j < a.Length
  // pre-conditions-end
  // post-conditions-start
  ensures forall k :: j <= k < j + a[j] && k < a.Length ==> a[k] != 0
  // post-conditions-end
{
// impl-start
  var i := j;
  while i < j + a[j] && i < a.Length
    invariant i < a.Length ==> a[j] - (i - j) <= a[i]
    invariant forall k :: j <= k < i && k < a.Length ==> a[k] != 0
    decreases j + a[j] - i
  {
    i := i + 1;
  }
// impl-end
}

method FindZero(a: array<int>) returns (index: int)
  // pre-conditions-start
  requires a != null
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i - 1] - 1 <= a[i]
  // pre-conditions-end
  // post-conditions-start
  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
  // post-conditions-end
{
// impl-start
  index := 0;
  while index < a.Length
    // invariants-start

    invariant 0 <= index
    invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != 0
    decreases a.Length - index
    // invariants-end

  {
    if a[index] == 0 {
      return;
    }
    // assert-start
    SkippingLemma(a, index);
    // assert-end

    index := index + a[index];
  }
  index := -1;
// impl-end
}
