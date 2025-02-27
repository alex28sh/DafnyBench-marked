// iron-sync_tmp_tmps49o3tyz_lib_Base_MapRemove.dfy


module {:extern} MapRemove_s {
  function {:opaque} MapRemove1<K, V>(m: map<K, V>, k: K): (m': map<K, V>)
    ensures forall j :: j in m && j != k ==> j in m'
    ensures forall j :: j in m' ==> j in m && j != k
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures k in m ==> |m'| == |m| - 1
    ensures k !in m ==> |m'| == |m|
  {
    var m' := map j | j in m && j != k :: m[j];
    assert m'.Keys == m.Keys - {k};
    m'
  }
  // pure-end

  method {:extern "MapRemove__s_Compile", "ComputeMapRemove1"} ComputeMapRemove1<K, V>(m: map<K, V>, k: K) returns (m': map<K, V>)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures m' == MapRemove1(m, k)
    // post-conditions-end
}
