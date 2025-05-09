function M1(f: map<int, bool>, i: int): bool
// pure-end

function M2(f: map<int, bool>, i: int): bool
{
  M1(map j | j in f :: f[j], i)
}
// pure-end

lemma L(f: map<int, bool>, i: int)
  // pre-conditions-start
  requires i in f
  requires M2(f, i)
  requires forall j: int, f: map<int, bool> :: M1(f, j) == (j in f && f[j])
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  assert f[i];
// impl-end
}
