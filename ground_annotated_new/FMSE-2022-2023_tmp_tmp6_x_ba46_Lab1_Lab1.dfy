function IsOddNat(x: int): bool
{
  x >= 0 &&
  x % 2 == 1
}
// pure-end

function IsEvenNat(x: int): bool
{
  x >= 0 &&
  x % 2 == 0
}
// pure-end

lemma AdditionOfTwoOddsResultsInEven(x: int, y: int)
  // pre-conditions-start
  requires IsOddNat(x)
  requires IsOddNat(y)
  // pre-conditions-end
  // post-conditions-start
  ensures IsEvenNat(x + y)
  // post-conditions-end
{
// impl-start
  calc {
    IsOddNat(x);
    x % 2 == 1;
  }
  calc {
    IsOddNat(y);
    y % 2 == 1;
  }
  calc {
    (x + y) % 2 == 0;
    IsEvenNat(x + y);
    true;
  }
// impl-end
}

function IsPrime(x: int): bool
  requires x >= 0
{
  x == 2 || forall d :: 2 <= d < x ==> x % d != 0
}
// pure-end

lemma AnyPrimeGreaterThanTwoIsOdd(x: int)
  // pre-conditions-start
  requires x > 2
  requires IsPrime(x)
  // pre-conditions-end
  // post-conditions-start
  ensures IsOddNat(x)
  // post-conditions-end
{
// impl-start
  calc {
    x % 2;
    {
      assert forall d :: 2 <= d < x ==> x % d != 0;
    }
    1;
  }
  calc {
    IsOddNat(x);
    x >= 0 &&
    x % 2 == 1;
    {
      assert x > 2;
    }
    true &&
    true;
    true;
  }
// impl-end
}

function add(x: int32, y: int32): int32
{
  if -2147483648 <= x as int + y as int <= 2147483647 then
    x + y
  else
    0
}
// pure-end

function sub(x: int32, y: int32): int32
{
  if -2147483648 <= x as int - y as int <= 2147483647 then
    x - y
  else
    0
}
// pure-end

function mul(x: int32, y: int32): int32
{
  if -2147483648 <= x as int * y as int <= 2147483647 then
    x * y
  else
    0
}
// pure-end

function div(x: int32, y: int32): int32
  requires y != 0
{
  if -2147483648 <= x as int / y as int <= 2147483647 then
    x / y
  else
    0
}
// pure-end

function mod(x: int32, y: int32): int32
  requires y != 0
{
  x % y
}
// pure-end

function abs(x: int32): (r: int32)
  ensures r >= 0
{
  if x == -2147483648 then
    0
  else if x < 0 then
    -x
  else
    x
}
// pure-end

newtype Odd = n: int
  | IsOddNat(n)
  witness 1

newtype Even = n: int
  | IsEvenNat(n)
  witness 2

newtype int32 = n: int
  | -2147483648 <= n < 2147483648
  witness 3
