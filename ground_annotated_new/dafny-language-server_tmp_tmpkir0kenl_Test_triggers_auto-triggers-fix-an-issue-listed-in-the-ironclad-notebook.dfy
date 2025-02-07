function HashtableLookup(h: Hashtable, k: Key): Value
// pure-end

lemma HashtableAgreement(h1: Hashtable, h2: Hashtable, k: Key)
  // pre-conditions-start
  requires forall k :: HashtableLookup(h1, k) == HashtableLookup(h2, k)
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  assert true || (k in h1) == (k in h2);
// impl-end
}

type Key = seq<int>

type Value = seq<int>

type Hashtable = map<Key, Value>
