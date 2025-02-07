method AssignmentsToMark(students: int, tutors: int) returns (r: int)
  // pre-conditions-start
  requires students > 0 && tutors > 1
  // pre-conditions-end
  // post-conditions-start
  ensures r < students
  // post-conditions-end
{
// impl-start
  // assert-start
  assert students > 0 && tutors > 1;
  // assert-end

  // assert-start
  assert students > 0 && tutors > 1 && true;
  // assert-end

  // assert-start
  assert students > 0 && tutors > 1 && students / tutors < students ==> students / tutors < students;
  // assert-end

  // assert-start
  DivisionLemma(students, tutors);
  // assert-end

  // assert-start
  assert students / tutors < students;
  // assert-end

  r := students / tutors;
  // assert-start
  assert r < students;
  // assert-end

  calc {
    1 / tutors < 1;
    students / tutors < students;
  }
// impl-end
}

lemma DivisionLemma(n: int, d: int)
  // pre-conditions-start
  requires n > 0 && d > 1
  // pre-conditions-end
  // post-conditions-start
  ensures n / d < n
  // post-conditions-end

method AssignmentsToMarkOne(students: int, tutors: int) returns (r: int)
  // pre-conditions-start
  requires students > 0 && tutors > 1
  // pre-conditions-end
  // post-conditions-start
  ensures r < students
  // post-conditions-end
{
// impl-start
  r := students / tutors;
  calc == {
    true;
    1 / tutors < 1;
    students / tutors < students;
  }
// impl-end
}

lemma CommonElement(a: array<nat>, b: array<nat>)
  // pre-conditions-start
  requires a.Length > 0 && b.Length > 0 && a[0] == b[0]
  // pre-conditions-end
  // post-conditions-start
  ensures multiset(a[..]) * multiset(b[..]) == multiset([a[0]]) + multiset(a[1..]) * multiset(b[1..])
  // post-conditions-end
