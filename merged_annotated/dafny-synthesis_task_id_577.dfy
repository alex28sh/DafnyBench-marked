function Factorial(n: int): int
  requires n >= 0
  ensures 0 <= Factorial(n)
{
  if n == 0 then
    1
  else
    n * Factorial(n - 1)
}
// pure-end

method FactorialOfLastDigit(n: int) returns (fact: int)
  // pre-conditions-start
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures fact == Factorial(n % 10)
  // post-conditions-end
{
// impl-start
  var lastDigit := n % 10;
  fact := Factorial(lastDigit);
// impl-end
}
