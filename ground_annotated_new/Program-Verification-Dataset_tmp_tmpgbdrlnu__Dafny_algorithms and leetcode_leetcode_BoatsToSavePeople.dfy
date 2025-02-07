function sumBoat(s: seq<nat>): nat
  requires 1 <= |s| <= 2
{
  if |s| == 1 then
    s[0]
  else
    s[0] + s[1]
}
// pure-end

function isSafeBoat(boat: seq<nat>, limit: nat): bool
{
  1 <= |boat| <= 2 &&
  sumBoat(boat) <= limit
}
// pure-end

function multisetAdd(ss: seq<seq<nat>>): multiset<nat>
{
  if ss == [] then
    multiset{}
  else
    multiset(ss[0]) + multisetAdd(ss[1..])
}
// pure-end

function multisetEqual(ss: seq<seq<nat>>, xs: seq<nat>): bool
{
  multiset(xs) == multisetAdd(ss)
}
// pure-end

function allSafe(boats: seq<seq<nat>>, limit: nat): bool
{
  forall boat :: 
    boat in boats ==>
      isSafeBoat(boat, limit)
}
// pure-end

function sorted(list: seq<int>): bool
{
  forall i, j :: 
    0 <= i < j < |list| ==>
      list[i] <= list[j]
}
// pure-end

method numRescueBoats(people: seq<nat>, limit: nat) returns (boats: nat)
  // pre-conditions-start
  requires |people| >= 1
  requires sorted(people)
  requires forall i: nat :: i < |people| ==> 1 <= people[i] <= limit
  // pre-conditions-end
  // post-conditions-start
  ensures exists boatConfig: seq<seq<nat>> :: multisetEqual(boatConfig, people) && allSafe(boatConfig, limit) && boats == |boatConfig|
  // post-conditions-end
{
// impl-start
  boats := 0;
  var lower: nat := 0;
  var upper: int := |people| - 1;
  ghost var visitedUpper: multiset<nat> := multiset{};
  ghost var visitedLower: multiset<nat> := multiset{};
  ghost var remaining: multiset<nat> := multiset(people);
  ghost var safeBoats: seq<seq<nat>> := [];
  while lower <= upper
    // invariants-start

    invariant 0 <= lower <= |people|
    invariant lower - 1 <= upper < |people|
    invariant visitedUpper == multiset(people[upper + 1..])
    invariant visitedLower == multiset(people[..lower])
    invariant allSafe(safeBoats, limit)
    invariant multisetAdd(safeBoats) == visitedLower + visitedUpper
    invariant |safeBoats| == boats
    // invariants-end

  {
    if people[upper] == limit || people[upper] + people[lower] > limit {
      boats := boats + 1;
      // assert-start
      assert isSafeBoat([people[upper]], limit);
      // assert-end

      safeBoats := [[people[upper]]] + safeBoats;
      // assert-start
      assert visitedUpper == multiset(people[upper + 1..]);
      // assert-end

      ghost var gu := people[upper + 1..];
      // assert-start
      assert multiset(gu) == visitedUpper;
      // assert-end

      // assert-start
      assert people[upper..] == [people[upper]] + gu;
      // assert-end

      visitedUpper := visitedUpper + multiset{people[upper]};
      upper := upper - 1;
      // assert-start
      assert people[upper + 1..] == [people[upper + 1]] + gu;
      // assert-end

    } else {
      ghost var gl := people[..lower];
      boats := boats + 1;
      if lower == upper {
        visitedLower := visitedLower + multiset{people[lower]};
        // assert-start
        assert isSafeBoat([people[lower]], limit);
        // assert-end

        safeBoats := [[people[lower]]] + safeBoats;
      } else {
        ghost var gu := people[upper + 1..];
        // assert-start
        assert multiset(gu) == visitedUpper;
        // assert-end

        visitedUpper := visitedUpper + multiset{people[upper]};
        visitedLower := visitedLower + multiset{people[lower]};
        // assert-start
        assert isSafeBoat([people[upper], people[lower]], limit);
        // assert-end

        safeBoats := [[people[upper], people[lower]]] + safeBoats;
        upper := upper - 1;
        // assert-start
        assert people[upper + 1..] == [people[upper + 1]] + gu;
        // assert-end

      }
      lower := lower + 1;
      // assert-start
      assert people[..lower] == gl + [people[lower - 1]];
      // assert-end

    }
  }
  // assert-start
  assert visitedLower == multiset(people[..lower]);
  // assert-end

  // assert-start
  assert visitedUpper == multiset(people[upper + 1..]);
  // assert-end

  // assert-start
  assert upper + 1 == lower;
  // assert-end

  // assert-start
  assert people == people[..lower] + people[upper + 1..];
  // assert-end

  // assert-start
  assert visitedLower + visitedUpper == multiset(people);
  // assert-end

// impl-end
}
