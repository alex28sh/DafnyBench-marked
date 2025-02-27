function last<T>(s: seq<T>): T
  requires |s| > 0
{
  s[|s| - 1]
}
// pure-end

function all_but_last<T>(s: seq<T>): seq<T>
  requires |s| > 0
  ensures |all_but_last(s)| == |s| - 1
{
  s[..|s| - 1]
}
// pure-end

function ConcatenateSeqs<T>(ss: seq<seq<T>>): seq<T>
{
  if |ss| == 0 then
    []
  else
    ss[0] + ConcatenateSeqs(ss[1..])
}
// pure-end

lemma {:axiom} lemma_ReverseConcatenateSeqs<T>(ss: seq<seq<T>>)
  // pre-conditions-start
  requires |ss| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures ConcatenateSeqs(ss) == ConcatenateSeqs(all_but_last(ss)) + last(ss)
  // post-conditions-end

lemma Test(word_seqs: seq<seq<uint32>>, words: seq<uint32>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var word_seqs' := word_seqs + [words];
  calc {
    ConcatenateSeqs(word_seqs');
    {
      lemma_ReverseConcatenateSeqs(word_seqs');
    }
    ConcatenateSeqs(all_but_last(word_seqs')) + last(word_seqs');
  }
// impl-end
}

lemma AltTest(word_seqs: seq<seq<uint32>>, words: seq<uint32>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var word_seqs' := word_seqs + [words];
  assert last(word_seqs') == words;
  assert ConcatenateSeqs(word_seqs) + last(word_seqs') == ConcatenateSeqs(word_seqs) + words;
// impl-end
}

function f<T>(s: seq<T>): seq<T>
// pure-end

function g<T>(ss: seq<seq<T>>): seq<T>
// pure-end

lemma {:axiom} lemma_fg<T>(s: seq<seq<T>>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures g(s) == g(f(s))
  // post-conditions-end

lemma Test2(s: seq<seq<uint32>>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  calc {
    g(s);
    {
      lemma_fg(s);
    }
    g(f(s));
  }
// impl-end
}

lemma AltTest2(s: seq<seq<uint32>>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  lemma_fg(s);
  assert g(s) == g(f(s));
// impl-end
}

type uint32 = i: int
  | 0 <= i < 4294967296
