function exp(x: int, e: int): int
  requires e >= 0
  ensures x > 0 ==> exp(x, e) > 0
  decreases e
{
  if e == 0 then
    1
  else
    x * exp(x, e - 1)
}
// pure-end

lemma exp3_Lemma(n: int)
  // pre-conditions-start
  requires n >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures (exp(3, n) - 1) % 2 == 0
  decreases n
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma mult8_Lemma(n: int)
  // pre-conditions-start
  requires n >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures (exp(3, 2 * n) - 1) % 8 == 0
  decreases n
  // post-conditions-end
{
// impl-start
  if n == 1 {
  } else {
    calc == {
      (exp(3, 2 * n) - 1) % 8;
      (exp(3, 2 * (n - 1)) * 8 + exp(3, 2 * (n - 1)) - 1) % 8;
      {
        mult8_Lemma(n - 1);
        assert exp(3, 2 * (n - 1)) * 8 % 8 == 0;
      }
      0;
    }
  }
// impl-end
}
