function IsEven(a: int): bool
  requires a >= 0
{
  if a == 0 then
    true
  else if a == 1 then
    false
  else
    IsEven(a - 2)
}
// pure-end

lemma EvenSquare(a: int)
  // pre-conditions-start
  requires a >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures IsEven(a) ==> IsEven(a * a)
  // post-conditions-end
{
// impl-start
  if a >= 2 && IsEven(a) {
    EvenSquare(a - 2);
    assert a * a == (a - 2) * (a - 2) + 4 * a - 4;
    EvenDouble(2 * a - 2);
    EvenPlus((a - 2) * (a - 2), 4 * a - 4);
  }
// impl-end
}

lemma EvenDouble(a: int)
  // pre-conditions-start
  requires a >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures IsEven(a + a)
  // post-conditions-end
{
// impl-start
  if a >= 2 {
    EvenDouble(a - 2);
  }
// impl-end
}

lemma {:induction x} EvenPlus(x: int, y: int)
  // pre-conditions-start
  requires x >= 0
  requires y >= 0
  requires IsEven(x)
  requires IsEven(y)
  // pre-conditions-end
  // post-conditions-start
  ensures IsEven(x + y)
  // post-conditions-end
{
// impl-start
  if x >= 2 {
    EvenPlus(x - 2, y);
  }
// impl-end
}
