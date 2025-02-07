method Find(blood: array<int>, key: int) returns (index: int)
  // pre-conditions-start
  requires blood != null
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= index ==> index < blood.Length && blood[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < blood.Length ==> blood[k] != key
  // post-conditions-end
{
// impl-start
  index := 0;
  while index < blood.Length
    // invariants-start

    invariant 0 <= index <= blood.Length
    invariant forall k :: 0 <= k < index ==> blood[k] != key
    // invariants-end

  {
    if blood[index] == key {
      return;
    }
    index := index + 1;
  }
  index := -1;
// impl-end
}
