function maxcheck(s: array<nat>, i: int, max: int): int
  requires 0 <= i <= s.Length
  reads s
{
  if i == 0 then
    max
  else if s[i - 1] > max then
    maxcheck(s, i - 1, s[i - 1])
  else
    maxcheck(s, i - 1, max)
}
// pure-end

method max(s: array<nat>) returns (a: int)
  // pre-conditions-start
  requires s.Length > 0
  // pre-conditions-end
  // post-conditions-start
  ensures forall x :: 0 <= x < s.Length ==> a >= s[x]
  ensures a in s[..]
  // post-conditions-end
{
// impl-start
  a := s[0];
  var i: int := 0;
  while i < s.Length
    // invariants-start

    invariant 0 <= i <= s.Length
    invariant forall x :: 0 <= x < i ==> a >= s[x]
    invariant a in s[..]
    // invariants-end

  {
    if s[i] > a {
      a := s[i];
    }
    i := i + 1;
  }
// impl-end
}

method Checker()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a := new nat[] [1, 2, 3, 50, 5, 51];
  var n := max(a);
  // assert-start
  assert n == 51;
  // assert-end

// impl-end
}
