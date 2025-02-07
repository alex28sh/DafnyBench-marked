lemma {:induction false} Divby2(n: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures n * (n - 1) % 2 == 0
  // post-conditions-end
{
// impl-start
  if n == 0 {
    assert 1 * (1 - 1) % 2 == 0;
  } else {
    Divby2(n - 1);
    assert (n - 1) * (n - 2) == n * n - 3 * n + 2;
  }
// impl-end
}
