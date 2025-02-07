function pow(base: int, exponent: int): int
  requires exponent >= 0
  decreases exponent
{
  if exponent == 0 then
    1
  else if exponent % 2 == 0 then
    pow(base * base, exponent / 2)
  else
    base * pow(base, exponent - 1)
}
// pure-end

method do_algebra(operators: seq<char>, operands: seq<int>) returns (result: int)
  // pre-conditions-start
  requires operators != [] && operands != [] && |operators| + 1 == |operands|
  requires forall i :: 0 <= i < |operands| ==> operands[i] >= 0
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  result := operands[0];
  var i := 0;
  while i < |operators|
    // invariants-start

    invariant 0 <= i <= |operators|
    decreases |operators| - i
    // invariants-end

  {
    var op := operators[i];
    i := i + 1;
    match op {
      case {:split false} '+' =>
        result := result + operands[i];
      case {:split false} '-' =>
        result := result - operands[i];
      case {:split false} '*' =>
        result := result * operands[i];
      case {:split false} '/' =>
        if operands[i] != 0 {
          result := result / operands[i];
        }
      case {:split false} '^' =>
        result := pow(result, operands[i]);
      case {:split false} _ /* _v0 */ =>
    }
  }
// impl-end
}
