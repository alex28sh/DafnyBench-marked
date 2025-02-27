lemma lemma_vacuous_statement_about_a_sequence(intseq: seq<int>, j: int)
  // pre-conditions-start
  requires 0 <= j < |intseq|
  // pre-conditions-end
  // post-conditions-start
  ensures intseq[0 .. j] == intseq[..j]
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma lemma_painful_statement_about_a_sequence(intseq: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures intseq == intseq[..|intseq|]
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma lemma_obvious_statement_about_a_sequence(boolseq: seq<bool>, j: int)
  // pre-conditions-start
  requires 0 <= j < |boolseq| - 1
  // pre-conditions-end
  // post-conditions-start
  ensures boolseq[1..][j] == boolseq[j + 1]
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma lemma_obvious_statement_about_a_sequence_int(intseq: seq<int>, j: int)
  // pre-conditions-start
  requires 0 <= j < |intseq| - 1
  // pre-conditions-end
  // post-conditions-start
  ensures intseq[1..][j] == intseq[j + 1]
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma lemma_straightforward_statement_about_a_sequence(intseq: seq<int>, j: int)
  // pre-conditions-start
  requires 0 <= j < |intseq|
  // pre-conditions-end
  // post-conditions-start
  ensures intseq[..j] + intseq[j..] == intseq
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma lemma_sequence_reduction(s: seq<int>, b: nat)
  // pre-conditions-start
  requires 0 < b < |s|
  // pre-conditions-end
  // post-conditions-start
  ensures s[0 .. b][0 .. b - 1] == s[0 .. b - 1]
  // post-conditions-end
{
// impl-start
  var t := s[0 .. b];
  forall i | 0 <= i < b - 1
    ensures s[0 .. b][0 .. b - 1][i] == s[0 .. b - 1][i]
  {
  }
// impl-end
}

lemma lemma_seq_concatenation_associative(a: seq<int>, b: seq<int>, c: seq<int>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures a + b + c == a + (b + c)
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma lemma_subseq_concatenation(s: seq<int>, left: int, middle: int, right: int)
  // pre-conditions-start
  requires 0 <= left <= middle <= right <= |s|
  // pre-conditions-end
  // post-conditions-start
  ensures s[left .. right] == s[left .. middle] + s[middle .. right]
  // post-conditions-end
{
// impl-start
// impl-end
}

lemma lemma_seq_equality(a: seq<int>, b: seq<int>, len: int)
  // pre-conditions-start
  requires |a| == |b| == len
  requires forall i {:trigger a[i]} {:trigger b[i]} :: 0 <= i < len ==> a[i] == b[i]
  // pre-conditions-end
  // post-conditions-start
  ensures a == b
  // post-conditions-end
{
// impl-start
  assert forall i :: 0 <= i < len ==> a[i] == b[i];
// impl-end
}

lemma lemma_seq_suffix(s: seq<int>, prefix_length: int, index: int)
  // pre-conditions-start
  requires 0 <= prefix_length <= index < |s|
  // pre-conditions-end
  // post-conditions-start
  ensures s[index] == s[prefix_length..][index - prefix_length]
  // post-conditions-end
{
// impl-start
// impl-end
}
