method FindPositionOfElement(a: array<int>, Element: nat, n1: nat, s1: seq<int>)
    returns (Position: int, Count: nat)
  // pre-conditions-start
  requires n1 == |s1| && 0 <= n1 <= a.Length
  requires forall i :: 0 <= i < |s1| ==> a[i] == s1[i]
  // pre-conditions-end
  // post-conditions-start
  ensures Position == -1 || Position >= 1
  ensures |s1| != 0 && Position >= 1 ==> exists i :: 0 <= i < |s1| && s1[i] == Element
  // post-conditions-end
{
// impl-start
  Count := 0;
  Position := 0;
  while Count != n1
    // invariants-start

    invariant |s1| != 0 && Position >= 1 ==> exists i :: 0 <= i < n1 && a[i] == Element
    invariant 0 <= Count <= n1
    invariant Position >= 1 ==> forall i :: 0 <= i < Count ==> a[i] != Element
    invariant Position == -1 ==> forall i :: 0 <= i < n1 ==> a[i] != Element
    decreases n1 - Count
    // invariants-end

  {
    if a[n1 - 1 - Count] == Element {
      Position := Count + 1;
      return Position, Count;
    }
    Count := Count + 1;
  }
  // assert-start
  assert Position != -1 ==> true;
  // assert-end

  Position := -1;
  // assert-start
  assert Position == -1;
  // assert-end

// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new int[5];
  var b := [1, 2, 3, 4];
  a[0], a[1], a[2], a[3] := 1, 2, 3, 4;
  var n1 := |b|;
  var Element := 5;
  var Position, Count;
  Position, Count := FindPositionOfElement(a, Element, n1, b);
  print "position is ", Position;
// impl-end
}
