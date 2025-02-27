method GetEven(s: array<nat>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies s
  ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) % 2 == 1 then s[i] == old(s[i]) + 1 else s[i] == old(s[i])
  // post-conditions-end
{
// impl-start
  var i := 0;
  while i < s.Length
    // invariants-start

    invariant 0 <= i <= s.Length
    invariant forall j :: 0 <= j < i ==> if old(s[j]) % 2 == 1 then s[j] == old(s[j]) + 1 else s[j] == old(s[j])
    invariant forall j :: i <= j < s.Length ==> s[j] == old(s[j])
    // invariants-end

  {
    if s[i] % 2 == 1 {
      s[i] := s[i] + 1;
    }
    i := i + 1;
  }
// impl-end
}

method evenTest()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var a: array<nat> := new nat[] [0, 9, 4];
  // assert-start
  assert a[0] == 0 && a[1] == 9 && a[2] == 4;
  // assert-end

  GetEven(a);
  // assert-start
  assert a[0] == 0 && a[1] == 10 && a[2] == 4;
  // assert-end

// impl-end
}
