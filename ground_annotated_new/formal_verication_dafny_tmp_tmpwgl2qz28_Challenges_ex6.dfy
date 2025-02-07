function bullspec(s: seq<nat>, u: seq<nat>): nat
  requires 0 <= |u| == |s| && nomultiples(u)
{
  reccbull(s, u, 0)
}
// pure-end

function cowspec(s: seq<nat>, u: seq<nat>): nat
  requires 0 <= |u| == |s| && nomultiples(u)
{
  recccow(s, u, 0)
}
// pure-end

function reccbull(s: seq<nat>, u: seq<nat>, i: int): nat
  requires 0 <= i <= |s| == |u|
  decreases |s| - i
{
  if i == |s| then
    0
  else if s[i] == u[i] then
    reccbull(s, u, i + 1) + 1
  else
    reccbull(s, u, i + 1)
}
// pure-end

function recccow(s: seq<nat>, u: seq<nat>, i: int): nat
  requires 0 <= i <= |s| == |u|
  decreases |s| - i
{
  if i == |s| then
    0
  else if s[i] != u[i] && u[i] in s then
    recccow(s, u, i + 1) + 1
  else
    recccow(s, u, i + 1)
}
// pure-end

function nomultiples(u: seq<nat>): bool
{
  forall j, k :: 
    0 <= j < k < |u| ==>
      u[j] != u[k]
}
// pure-end

method BullsCows(s: seq<nat>, u: seq<nat>)
    returns (b: nat, c: nat)
  // pre-conditions-start
  requires 0 < |u| == |s| <= 10
  requires nomultiples(u) && nomultiples(s)
  // pre-conditions-end
  // post-conditions-start
  ensures b >= 0 && c >= 0
  ensures b == bullspec(s, u)
  ensures c == cowspec(s, u)
  // post-conditions-end
{
// impl-start
  b, c := 0, 0;
  var i: int := |s|;
  while i > 0
    // invariants-start

    invariant 0 <= i <= |s| == |u|
    invariant b >= 0 && c >= 0
    invariant b == reccbull(s, u, i)
    invariant c == recccow(s, u, i)
    decreases i
    // invariants-end

  {
    i := i - 1;
    if s[i] != u[i] && u[i] in s {
      c := c + 1;
    } else if s[i] == u[i] {
      b := b + 1;
    }
  }
  return b, c;
// impl-end
}

method TEST()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var sys: seq<nat> := [1, 2, 9, 10];
  var usr: seq<nat> := [1, 2, 3, 7];
  // assert-start
  assert bullspec(sys, usr) == 2;
  // assert-end

  // assert-start
  assert cowspec(sys, usr) == 0;
  // assert-end

  var b: nat, c: nat := BullsCows(sys, usr);
  // assert-start
  assert b == 2 && c == 0;
  // assert-end

  var sys1: seq<nat> := [1, 2, 3, 4];
  var usr2: seq<nat> := [4, 3, 2, 1];
  // assert-start
  assert bullspec(sys1, usr2) == 0;
  // assert-end

  // assert-start
  assert cowspec(sys1, usr2) == 4;
  // assert-end

  b, c := BullsCows(sys1, usr2);
  // assert-start
  assert b == 0 && c == 4;
  // assert-end

  var sys3: seq<nat> := [1, 2, 3, 4, 5, 6, 7];
  var usr3: seq<nat> := [1, 2, 3, 4, 5, 6, 7];
  // assert-start
  assert bullspec(sys3, usr3) == 7;
  // assert-end

  // assert-start
  assert cowspec(sys3, usr3) == 0;
  // assert-end

  b, c := BullsCows(sys3, usr3);
  // assert-start
  assert b == 7 && c == 0;
  // assert-end

  var sys4: seq<nat> := [1, 2, 3, 4, 5, 6, 7];
  var usr4: seq<nat> := [1, 2, 3, 7, 8, 6, 5];
  // assert-start
  assert bullspec(sys4, usr4) == 4;
  // assert-end

  // assert-start
  assert cowspec(sys4, usr4) == 2;
  // assert-end

  b, c := BullsCows(sys4, usr4);
// impl-end
}
