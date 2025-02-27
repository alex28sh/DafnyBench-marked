// CS5232_Project_tmp_tmpai_cfrng_LFUSimple.dfy

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var lfuCache := new LFUCache(5);
  print "Cache Capacity = 5 \n";
  print "PUT (1, 1) - ";
  lfuCache.put(1, 1);
  print "PUT (2, 2) - ";
  lfuCache.put(2, 2);
  print "PUT (3, 3) - ";
  lfuCache.put(3, 3);
  print "GET (1) - ";
  var val := lfuCache.get(1);
  print "get(1) = ";
  print val;
  print "\n";
  print "PUT (3, 5) - ";
  lfuCache.put(3, 5);
  print "GET (3) - ";
  val := lfuCache.get(3);
  print "get(3) = ";
  print val;
  print "\n";
  print "PUT (4, 6) - ";
  lfuCache.put(4, 6);
  print "PUT (5, 7) - ";
  lfuCache.put(5, 7);
  print "PUT (10, 100) - ";
  lfuCache.put(10, 100);
  print "GET (2) - ";
  val := lfuCache.get(2);
  print "get(2) = ";
  print val;
  print "\n";
// impl-end
}

class LFUCache {
  var capacity: int
  var cacheMap: map<int, (int, int)>

  constructor (capacity: int)
    // pre-conditions-start
    requires capacity > 0
    // pre-conditions-end
    // post-conditions-start
    ensures this.Valid()
    // post-conditions-end
  {
  // impl-start
    this.capacity := capacity;
    this.cacheMap := map[];
  // impl-end
  }

  predicate Valid()
    reads this
  {
    this.capacity > 0 &&
    0 <= |this.cacheMap| <= this.capacity &&
    (|this.cacheMap| > 0 ==>
      forall e :: 
        e in this.cacheMap ==>
          this.cacheMap[e].1 >= 1) &&
    (|this.cacheMap| > 0 ==>
      forall e :: 
        e in this.cacheMap ==>
          this.cacheMap[e].0 >= 0)
  }
  // pure-end

  method getLFUKey() returns (lfuKey: int)
    // pre-conditions-start
    requires this.Valid()
    requires |this.cacheMap| > 0
    // pre-conditions-end
    // post-conditions-start
    ensures this.Valid()
    ensures lfuKey in this.cacheMap
    ensures forall k :: k in this.cacheMap.Items ==> this.cacheMap[lfuKey].1 <= this.cacheMap[k.0].1
    // post-conditions-end
  {
  // impl-start
    var items := this.cacheMap.Items;
    var seenItems := {};
    var anyItem :| anyItem in items;
    var minFreq := anyItem.1.1;
    lfuKey := anyItem.0;
    while items != {}
      // invariants-start

      invariant this.cacheMap.Items >= items
      invariant this.cacheMap.Items >= seenItems
      invariant this.cacheMap.Items == seenItems + items
      invariant lfuKey in this.cacheMap
      invariant this.cacheMap[lfuKey].1 == minFreq
      invariant forall e :: e in seenItems ==> minFreq <= e.1.1
      invariant forall e :: e in seenItems ==> minFreq <= this.cacheMap[e.0].1
      invariant forall e :: e in seenItems ==> this.cacheMap[lfuKey].1 <= this.cacheMap[e.0].1
      invariant exists e :: e in seenItems + items ==> minFreq == e.1.1
      decreases |items|
      // invariants-end

    {
      var item :| item in items;
      if item.1.1 < minFreq {
        lfuKey := item.0;
        minFreq := item.1.1;
      }
      items := items - {item};
      seenItems := seenItems + {item};
    }
    // assert-start
    assert seenItems == this.cacheMap.Items;
    // assert-end

    // assert-start
    assert this.cacheMap[lfuKey].1 == minFreq;
    // assert-end

    // assert-start
    assert forall e :: e in seenItems ==> minFreq <= e.1.1;
    // assert-end

    // assert-start
    assert forall e :: e in this.cacheMap.Items ==> minFreq <= e.1.1;
    // assert-end

    // assert-start
    assert forall k :: k in seenItems ==> this.cacheMap[lfuKey].1 <= this.cacheMap[k.0].1;
    // assert-end

    // assert-start
    assert forall k :: k in this.cacheMap.Items ==> this.cacheMap[lfuKey].1 <= this.cacheMap[k.0].1;
    // assert-end

    return lfuKey;
  // impl-end
  }

  method get(key: int) returns (value: int)
    // pre-conditions-start
    requires this.Valid()
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.Valid()
    ensures key !in this.cacheMap ==> value == -1
    ensures forall e :: e in old(this.cacheMap) <==> e in this.cacheMap
    ensures forall e :: e in old(this.cacheMap) ==> old(this.cacheMap[e].0) == this.cacheMap[e].0
    ensures key in this.cacheMap ==> value == this.cacheMap[key].0 && old(this.cacheMap[key].1) == this.cacheMap[key].1 - 1
    // post-conditions-end
  {
  // impl-start
    // assert-start
    assert key in this.cacheMap ==> this.cacheMap[key].0 >= 0;
    // assert-end

    if key !in this.cacheMap {
      value := -1;
    } else {
      // assert-start
      assert key in this.cacheMap;
      // assert-end

      // assert-start
      assert this.cacheMap[key].0 >= 0;
      // assert-end

      value := this.cacheMap[key].0;
      var oldFreq := this.cacheMap[key].1;
      var newV := (value, oldFreq + 1);
      this.cacheMap := this.cacheMap[key := newV];
    }
    print "after get: ";
    print this.cacheMap;
    print "\n";
    return value;
  // impl-end
  }

  method put(key: int, value: int)
    // pre-conditions-start
    requires this.Valid()
    requires value > 0
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.Valid()
    // post-conditions-end
  {
  // impl-start
    if key in this.cacheMap {
      var currFreq := this.cacheMap[key].1;
      this.cacheMap := this.cacheMap[key := (value, currFreq)];
    } else {
      if |this.cacheMap| < this.capacity {
        this.cacheMap := this.cacheMap[key := (value, 1)];
      } else {
        var LFUKey := this.getLFUKey();
        // assert-start
        assert LFUKey in this.cacheMap;
        // assert-end

        // assert-start
        assert |this.cacheMap| == this.capacity;
        // assert-end

        ghost var oldMap := this.cacheMap;
        var newMap := this.cacheMap - {LFUKey};
        this.cacheMap := newMap;
        // assert-start
        assert newMap == this.cacheMap - {LFUKey};
        // assert-end

        // assert-start
        assert LFUKey !in this.cacheMap;
        // assert-end

        // assert-start
        assert LFUKey in oldMap;
        // assert-end

        ghost var oldCard := |oldMap|;
        ghost var newCard := |newMap|;
        // assert-start
        assert |this.cacheMap.Keys| < |oldMap|;
        // assert-end

        this.cacheMap := this.cacheMap[key := (value, 1)];
      }
    }
    print "after put: ";
    print this.cacheMap;
    print "\n";
  // impl-end
  }
}
