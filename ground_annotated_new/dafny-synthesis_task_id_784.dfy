function IsEven(n: int): bool
{
  n % 2 == 0
}
// pure-end

function IsOdd(n: int): bool
{
  n % 2 != 0
}
// pure-end

function IsFirstEven(evenIndex: int, lst: seq<int>): bool
  requires 0 <= evenIndex < |lst|
  requires IsEven(lst[evenIndex])
{
  forall i :: 
    0 <= i < evenIndex ==>
      IsOdd(lst[i])
}
// pure-end

function IsFirstOdd(oddIndex: int, lst: seq<int>): bool
  requires 0 <= oddIndex < |lst|
  requires IsOdd(lst[oddIndex])
{
  forall i :: 
    0 <= i < oddIndex ==>
      IsEven(lst[i])
}
// pure-end

method FirstEvenOddIndices(lst: seq<int>) returns (evenIndex: int, oddIndex: int)
  // pre-conditions-start
  requires |lst| >= 2
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  // pre-conditions-end
  // post-conditions-start
  ensures 0 <= evenIndex < |lst|
  ensures 0 <= oddIndex < |lst|
  ensures IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
  ensures IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
  // post-conditions-end
{
// impl-start
  for i := 0 to |lst|
    // invariants-start

    invariant 0 <= i <= |lst|
    invariant forall j :: 0 <= j < i ==> IsOdd(lst[j])
    // invariants-end

  {
    if IsEven(lst[i]) {
      evenIndex := i;
      break;
    }
  }
  for i := 0 to |lst|
    // invariants-start

    invariant 0 <= i <= |lst|
    invariant forall j :: 0 <= j < i ==> IsEven(lst[j])
    // invariants-end

  {
    if IsOdd(lst[i]) {
      oddIndex := i;
      break;
    }
  }
// impl-end
}

method ProductEvenOdd(lst: seq<int>) returns (product: int)
  // pre-conditions-start
  requires |lst| >= 2
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  // pre-conditions-end
  // post-conditions-start
  ensures exists i, j :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst) && 0 <= j < |lst| && IsOdd(lst[j]) && IsFirstOdd(j, lst) && product == lst[i] * lst[j]
  // post-conditions-end
{
// impl-start
  var evenIndex, oddIndex := FirstEvenOddIndices(lst);
  product := lst[evenIndex] * lst[oddIndex];
// impl-end
}
