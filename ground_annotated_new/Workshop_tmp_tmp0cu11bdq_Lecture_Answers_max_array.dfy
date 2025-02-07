method max(a: array<int>) returns (max: int)
  // pre-conditions-start
  requires a != null
  // pre-conditions-end
  // post-conditions-start
  ensures forall j :: j >= 0 && j < a.Length ==> max >= a[j]
  ensures a.Length > 0 ==> exists j :: j >= 0 && j < a.Length && max == a[j]
  // post-conditions-end
{
// impl-start
  if a.Length == 0 {
    max := 0;
    return;
  }
  max := a[0];
  var i := 1;
  while i < a.Length
    // invariants-start

    invariant i <= a.Length
    invariant forall j :: 0 <= j < i ==> max >= a[j]
    invariant exists j :: 0 <= j < i && max == a[j]
    // invariants-end

  {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
// impl-end
}
