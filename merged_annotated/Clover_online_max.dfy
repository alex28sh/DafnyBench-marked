method onlineMax(a: array<int>, x: int)
    returns (ghost m: int, p: int)
  // pre-conditions-start
  requires 1 <= x < a.Length
  requires a.Length != 0
  // pre-conditions-end
  // post-conditions-start
  ensures x <= p < a.Length
  ensures forall i :: 0 <= i < x ==> a[i] <= m
  ensures exists i :: 0 <= i < x && a[i] == m
  ensures x <= p < a.Length - 1 ==> forall i :: 0 <= i < p ==> a[i] < a[p]
  ensures (forall i :: x <= i < a.Length && a[i] <= m) ==> p == a.Length - 1
  // post-conditions-end
{
// impl-start
  p := 0;
  var best := a[0];
  var i := 1;
  while i < x
    // invariants-start

    invariant 0 <= i <= x
    invariant forall j :: 0 <= j < i ==> a[j] <= best
    invariant exists j :: 0 <= j < i && a[j] == best
    // invariants-end

  {
    if a[i] > best {
      best := a[i];
    }
    i := i + 1;
  }
  m := best;
  i := x;
  while i < a.Length
    // invariants-start

    invariant x <= i <= a.Length
    invariant forall j :: x <= j < i ==> a[j] <= m
    // invariants-end

  {
    if a[i] > best {
      p := i;
      return;
    }
    i := i + 1;
  }
  p := a.Length - 1;
// impl-end
}
