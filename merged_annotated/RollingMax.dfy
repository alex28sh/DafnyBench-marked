function isMax(m: int, numbers: seq<int>): bool
{
  m in numbers &&
  forall i :: 
    0 <= i < |numbers| ==>
      numbers[i] <= m
}
// pure-end

method max(numbers: seq<int>) returns (result: int)
  // pre-conditions-start
  requires numbers != []
  // pre-conditions-end
  // post-conditions-start
  ensures isMax(result, numbers)
  // post-conditions-end
{
// impl-start
  result := numbers[0];
  for i := 1 to |numbers|
    // invariants-start

    invariant isMax(result, numbers[0 .. i])
    // invariants-end

  {
    if numbers[i] > result {
      result := numbers[i];
    }
  }
// impl-end
}

method RollingMax(numbers: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires numbers != []
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == |numbers|
  ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0 .. i + 1])
  // post-conditions-end
{
// impl-start
  var m := numbers[0];
  result := [m];
  for i := 1 to |numbers|
    // invariants-start

    invariant |result| == i
    invariant m == result[i - 1]
    invariant forall j :: 0 <= j < i ==> isMax(result[j], numbers[0 .. j + 1])
    // invariants-end

  {
    if numbers[i] > m {
      m := numbers[i];
    }
    result := result + [m];
  }
// impl-end
}
