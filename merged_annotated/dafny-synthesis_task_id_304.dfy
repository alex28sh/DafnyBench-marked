method ElementAtIndexAfterRotation(l: seq<int>, n: int, index: int)
    returns (element: int)
  // pre-conditions-start
  requires n >= 0
  requires 0 <= index < |l|
  // pre-conditions-end
  // post-conditions-start
  ensures element == l[(index - n + |l|) % |l|]
  // post-conditions-end
{
// impl-start
  element := l[(index - n + |l|) % |l|];
// impl-end
}
