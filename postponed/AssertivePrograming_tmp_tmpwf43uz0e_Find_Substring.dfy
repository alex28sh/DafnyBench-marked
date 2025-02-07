function ExistsSubstring(str1: string, str2: string): bool
{
  exists offset :: 
    0 <= offset <= |str1| &&
    str2 <= str1[offset..]
}
// pure-end

function Post(str1: string, str2: string, found: bool, i: nat): bool
{
  (found <==> ExistsSubstring(str1, str2)) &&
  (found ==>
    i + |str2| <= |str1| &&
    str2 <= str1[i..])
}
// pure-end

method {:verify true} FindFirstOccurrence(str1: string, str2: string)
    returns (found: bool, i: nat)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures Post(str1, str2, found, i)
  // post-conditions-end
{
// impl-start
  if |str2| == 0 {
    found, i := true, 0;
    // assert-start
    assert Post(str1, str2, found, i);
    // assert-end

  } else if |str1| < |str2| {
    found, i := false, 0;
    // assert-start
    assert Post(str1, str2, found, i);
    // assert-end

  } else {
    found, i := false, |str2| - 1;
    // assert-start
    assert |str2| > 0;
    // assert-end

    // assert-start
    assert |str1| >= |str2|;
    // assert-end

    // assert-start
    assert Outter_Inv_correctness(str1, str2, false, |str2| - 1);
    // assert-end

    while !found && i < |str1|
      // invariants-start

      invariant Outter_Inv_correctness(str1, str2, found, i)
      decreases if !found then 1 else 0, |str1| - i
      // invariants-end

    {
      // assert-start
      assert Outter_Inv_correctness(str1, str2, found, i);
      // assert-end

      // assert-start
      assert |str2| > 0;
      // assert-end

      // assert-start
      assert !found && i < |str1|;
      // assert-end

      var j := |str2| - 1;
      ghost var old_i := i;
      ghost var old_j := j;
      while !found && str1[i] == str2[j]
        // invariants-start

        invariant Inner_Inv_Termination(str1, str2, i, j, old_i, old_j)
        invariant Inner_Inv_correctness(str1, str2, i, j, found)
        decreases j, if !found then 1 else 0
        // invariants-end

      {
        if j == 0 {
          // assert-start
          assert j == 0 && str1[i] == str2[j];
          // assert-end

          found := true;
          // assert-start
          assert Inner_Inv_Termination(str1, str2, i, j, old_i, old_j);
          // assert-end

          // assert-start
          assert Inner_Inv_correctness(str1, str2, i, j, found);
          // assert-end

        } else {
          // assert-start
          assert j > 0;
          // assert-end

          // assert-start
          assert Inner_Inv_Termination(str1, str2, i - 1, j - 1, old_i, old_j);
          // assert-end

          // assert-start
          assert Inner_Inv_correctness(str1, str2, i - 1, j - 1, found);
          // assert-end

          i, j := i - 1, j - 1;
          // assert-start
          assert Inner_Inv_Termination(str1, str2, i, j, old_i, old_j);
          // assert-end

          // assert-start
          assert Inner_Inv_correctness(str1, str2, i, j, found);
          // assert-end

        }
        // assert-start
        assert j >= 0;
        // assert-end

        // assert-start
        assert Inner_Inv_Termination(str1, str2, i, j, old_i, old_j);
        // assert-end

        // assert-start
        assert Inner_Inv_correctness(str1, str2, i, j, found);
        // assert-end

      }
      // assert-start
      assert Inner_Inv_Termination(str1, str2, i, j, old_i, old_j);
      // assert-end

      // assert-start
      assert Inner_Inv_correctness(str1, str2, i, j, found);
      // assert-end

      // assert-start
      assert found || str1[i] != str2[j];
      // assert-end

      // assert-start
      assert found ==> i + |str2| <= |str1| && str2 <= str1[i..];
      // assert-end

      // assert-start
      assert !found ==> str1[i] != str2[j];
      // assert-end

      if !found {
        // assert-start
        assert i < |str1|;
        // assert-end

        // assert-start
        assert |str2| > 0;
        // assert-end

        // assert-start
        assert old_j - j == old_i - i;
        // assert-end

        // assert-start
        assert old_i < i + |str2| - j;
        // assert-end

        // assert-start
        assert Outter_Inv_correctness(str1, str2, found, old_i);
        // assert-end

        // assert-start
        assert i + |str2| - j == old_i + 1;
        // assert-end

        // assert-start
        assert str1[i] != str2[j];
        // assert-end

        // assert-start
        assert |str1[old_i + 1 - |str2| .. old_i + 1]| == |str2|;
        // assert-end

        // assert-start
        assert str1[old_i + 1 - |str2| .. old_i + 1] != str2;
        // assert-end

        // assert-start
        assert 0 < old_i <= |str1| ==> !ExistsSubstring(str1[..old_i], str2);
        // assert-end

        // assert-start
        Lemma1(str1, str2, i, j, old_i, old_j, found);
        // assert-end

        // assert-start
        assert 0 < old_i + 1 <= |str1| ==> !ExistsSubstring(str1[..old_i + 1], str2);
        // assert-end

        // assert-start
        assert 0 < i + |str2| - j <= |str1| ==> !ExistsSubstring(str1[..i + |str2| - j], str2);
        // assert-end

        // assert-start
        assert Outter_Inv_correctness(str1, str2, found, i + |str2| - j);
        // assert-end

        i := i + |str2| - j;
        // assert-start
        assert old_i < i;
        // assert-end

        // assert-start
        assert Outter_Inv_correctness(str1, str2, found, i);
        // assert-end

        // assert-start
        assert i <= |str1|;
        // assert-end

      }
      // assert-start
      assert !found ==> i <= |str1|;
      // assert-end

      // assert-start
      assert !found ==> old_i < i;
      // assert-end

      // assert-start
      assert !found ==> Outter_Inv_correctness(str1, str2, found, i);
      // assert-end

      // assert-start
      assert found ==> Outter_Inv_correctness(str1, str2, found, i);
      // assert-end

      // assert-start
      assert Outter_Inv_correctness(str1, str2, found, i);
      // assert-end

    }
    // assert-start
    assert Outter_Inv_correctness(str1, str2, found, i);
    // assert-end

    // assert-start
    assert found ==> i + |str2| <= |str1| && str2 <= str1[i..];
    // assert-end

    // assert-start
    assert !found && 0 < i <= |str1| ==> !ExistsSubstring(str1[..i], str2);
    // assert-end

    // assert-start
    assert !found ==> i <= |str1|;
    // assert-end

    // assert-start
    assert found || i >= |str1|;
    // assert-end

    // assert-start
    assert !found && i == |str1| ==> !ExistsSubstring(str1[..i], str2);
    // assert-end

    // assert-start
    assert i == |str1| ==> str1[..i] == str1;
    // assert-end

    // assert-start
    assert !found && i == |str1| ==> !ExistsSubstring(str1, str2);
    // assert-end

    // assert-start
    assert !found ==> i >= |str1|;
    // assert-end

    // assert-start
    assert !found ==> i == |str1|;
    // assert-end

    // assert-start
    assert !found ==> !ExistsSubstring(str1, str2);
    // assert-end

    // assert-start
    assert found ==> ExistsSubstring(str1, str2);
    // assert-end

    // assert-start
    assert found <==> ExistsSubstring(str1, str2);
    // assert-end

    // assert-start
    assert found ==> i + |str2| <= |str1| && str2 <= str1[i..];
    // assert-end

    // assert-start
    assert Post(str1, str2, found, i);
    // assert-end

  }
  // assert-start
  assert Post(str1, str2, found, i);
  // assert-end

// impl-end
}

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var str1a, str1b := "string", " in Dafny is a sequence of characters (seq<char>)";
  var str1, str2 := str1a + str1b, "ring";
  var found, i := FindFirstOccurrence(str1, str2);
  // assert-start
  assert found by {
    assert ExistsSubstring(str1, str2) by {
      var offset := 2;
      assert 0 <= offset <= |str1|;
      assert str2 <= str1[offset..] by {
        assert str2 == str1[offset..][..4];
      }
    }
  }
  // assert-end

  print "\nfound, i := FindFirstOccurrence(\"", str1, "\", \"", str2, "\") returns found == ", found;
  if found {
    print " and i == ", i;
  }
  str1 := "<= on sequences is the prefix relation";
  found, i := FindFirstOccurrence(str1, str2);
  print "\nfound, i := FindFirstOccurrence(\"", str1, "\", \"", str2, "\") returns found == ", found;
  if found {
    print " and i == ", i;
  }
// impl-end
}

function Outter_Inv_correctness(str1: string, str2: string, found: bool, i: nat): bool
{
  (found ==>
    i + |str2| <= |str1| &&
    str2 <= str1[i..]) &&
  (!found &&
  0 < i <= |str1| &&
  i != |str2| - 1 ==>
    !ExistsSubstring(str1[..i], str2)) &&
  (!found ==>
    i <= |str1|)
}
// pure-end

function Inner_Inv_correctness(str1: string, str2: string, i: nat, j: int, found: bool): bool
{
  0 <= j <= i &&
  j < |str2| &&
  i < |str1| &&
  (str1[i] == str2[j] ==>
    str2[j..] <= str1[i..]) &&
  (found ==>
    j == 0 &&
    str1[i] == str2[j])
}
// pure-end

function Inner_Inv_Termination(str1: string, str2: string, i: nat, j: int, old_i: nat, old_j: nat): bool
{
  old_j - j == old_i - i
}
// pure-end

lemma {:verify true} Lemma1(str1: string, str2: string, i: nat, j: int, old_i: nat, old_j: nat, found: bool)
  // pre-conditions-start
  requires !found
  requires |str2| > 0
  requires Outter_Inv_correctness(str1, str2, found, old_i)
  requires i + |str2| - j == old_i + 1
  requires old_i + 1 >= |str2|
  requires old_i + 1 <= |str1|
  requires 0 <= i < |str1| && 0 <= j < |str2|
  requires str1[i] != str2[j]
  requires |str2| > 0
  requires 0 < old_i <= |str1| ==> !ExistsSubstring(str1[..old_i], str2)
  // pre-conditions-end
  // post-conditions-start
  ensures 0 < old_i + 1 <= |str1| ==> !ExistsSubstring(str1[..old_i + 1], str2)
  // post-conditions-end
{
// impl-start
  assert |str1[old_i + 1 - |str2| .. old_i + 1]| == |str2|;
  assert str1[old_i + 1 - |str2| .. old_i + 1] != str2;
  assert !(str2 <= str1[old_i + 1 - |str2| .. old_i + 1]);
  assert 0 <= old_i < old_i + 1 <= |str1|;
  assert old_i + 1 >= |str2|;
  calc {
    0 < old_i + 1 <= |str1| &&
    ExistsSubstring(str1[..old_i + 1], str2) &&
    !(str2 <= str1[old_i + 1 - |str2| .. old_i + 1]);
  ==>
    !ExistsSubstring(str1[..old_i], str2) &&
    ExistsSubstring(str1[..old_i + 1], str2) &&
    !(str2 <= str1[old_i + 1 - |str2| .. old_i + 1]);
  ==>
    {
      Lemma2(str1, str2, old_i, found);
    }
    (0 < old_i < old_i + 1 <= |str1| &&
    old_i != |str2| - 1 ==>
      |str1[old_i + 1 - |str2| .. old_i + 1]| == |str2| &&
      str2 <= str1[old_i + 1 - |str2| .. old_i + 1]) &&
    !(str2 <= str1[old_i + 1 - |str2| .. old_i + 1]);
  ==>
    0 < old_i < old_i + 1 <= |str1| &&
    old_i != |str2| - 1 ==>
      false;
  }
// impl-end
}

lemma {:verify true} Lemma2(str1: string, str2: string, i: nat, found: bool)
  // pre-conditions-start
  requires 0 <= i < |str1|
  requires 0 < |str2| <= i + 1
  requires !ExistsSubstring(str1[..i], str2)
  requires ExistsSubstring(str1[..i + 1], str2)
  // pre-conditions-end
  // post-conditions-start
  ensures str2 <= str1[i + 1 - |str2| .. i + 1]
  // post-conditions-end
{
// impl-start
  assert exists offset :: 0 <= offset <= i + 1 && str2 <= str1[offset .. i + 1] && (offset <= i || offset == i + 1);
  calc {
    0 < |str2| &&
    !(exists offset :: 0 <= offset <= i && str2 <= str1[offset .. i]) &&
    exists offset :: 
      0 <= offset <= i + 1 &&
      str2 <= str1[offset .. i + 1];
  ==>
    0 < |str2| &&
    (forall offset :: 
      0 <= offset <= i ==>
        !(str2 <= str1[offset .. i])) &&
    exists offset :: 
      0 <= offset <= i + 1 &&
      str2 <= str1[offset .. i + 1];
  ==>
    0 < |str2| &&
    (exists offset :: 
      0 <= offset <= i + 1 &&
      str2 <= str1[offset .. i + 1]) &&
    forall offset :: 
      0 <= offset <= i + 1 ==>
        offset <= i ==>
          !(str2 <= str1[offset .. i]);
  ==>
    {
      Lemma3(str1, str2, i);
    }
    0 < |str2| &&
    exists offset :: 
      0 <= offset <= i + 1 &&
      str2 <= str1[offset .. i + 1] &&
      (offset <= i ==>
        !(str2 <= str1[offset .. i]));
  ==>
    0 < |str2| &&
    exists offset :: 
      0 <= offset <= i + 1 &&
      str2 <= str1[offset .. i + 1] &&
      (offset <= i ==>
        !(str2 <= str1[offset .. i])) &&
      (offset == i + 1 ==>
        |str2| == 0);
  ==>
    0 < |str2| &&
    exists offset :: 
      0 <= offset <= i + 1 &&
      str2 <= str1[offset .. i + 1] &&
      (offset <= i ==>
        !(str2 <= str1[offset .. i])) &&
      (offset == i + 1 ==>
        |str2| == 0) &&
      offset != i + 1;
  ==>
    0 < |str2| &&
    exists offset :: 
      0 <= offset <= i + 1 &&
      str2 <= str1[offset .. i + 1] &&
      (offset <= i ==>
        !(str2 <= str1[offset .. i])) &&
      offset <= i;
  ==>
    0 < |str2| &&
    exists offset :: 
      0 <= offset <= i + 1 &&
      str2 <= str1[offset .. i + 1] &&
      !(str2 <= str1[offset .. i]);
  ==>
    str2 <= str1[i + 1 - |str2| .. i + 1];
  }
// impl-end
}

lemma Lemma3(str1: string, str2: string, i: nat)
  // pre-conditions-start
  requires 0 <= i < |str1|
  requires 0 < |str2| <= i + 1
  requires exists offset :: 0 <= offset <= i + 1 && str2 <= str1[offset .. i + 1]
  requires forall offset :: 0 <= offset <= i + 1 ==> offset <= i ==> !(str2 <= str1[offset .. i])
  // pre-conditions-end
  // post-conditions-start
  ensures exists offset :: 0 <= offset <= i + 1 && str2 <= str1[offset .. i + 1] && (offset <= i ==> !(str2 <= str1[offset .. i]))
  // post-conditions-end
{
// impl-start
  var offset :| 0 <= offset <= i + 1 && str2 <= str1[offset .. i + 1];
  assert 0 <= offset <= i + 1 ==> offset <= i ==> !(str2 <= str1[offset .. i]);
// impl-end
}
