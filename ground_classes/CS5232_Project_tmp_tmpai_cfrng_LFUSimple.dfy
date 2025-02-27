class LFUCache {

  var capacity : int;
  var cacheMap : map<int, (int, int)>; //key -> {value, freq}

  constructor(capacity: int)
    requires capacity > 0;
    ensures this.Valid();
  {
    this.capacity := capacity;
    this.cacheMap := map[];
  }

  predicate Valid()
    reads this;
    // reads this.freqMap.Values;
  {
    // general value check
    this.capacity > 0 &&
    0 <= |this.cacheMap| <= this.capacity &&
    (|this.cacheMap| > 0 ==> (forall e :: e in this.cacheMap ==> this.cacheMap[e].1 >= 1)) && // frequency should always larger than 0
    (|this.cacheMap| > 0 ==> (forall e :: e in this.cacheMap ==> this.cacheMap[e].0 >= 0)) // only allow positive values
  } 

  method getLFUKey() returns (lfuKey : int) 
    requires this.Valid();
    requires |this.cacheMap| > 0;
    ensures this.Valid();
    ensures lfuKey in this.cacheMap;
    ensures forall k :: k in this.cacheMap.Items ==> this.cacheMap[lfuKey].1 <= this.cacheMap[k.0].1;
  {
    var items := this.cacheMap.Items;
    var seenItems := {};

    var anyItem :| anyItem in items;
    var minFreq := anyItem.1.1;
    lfuKey := anyItem.0;

    while items != {}
    decreases |items|;
    invariant this.cacheMap.Items >= items;
    invariant this.cacheMap.Items >= seenItems;
    invariant this.cacheMap.Items == seenItems + items;
    invariant lfuKey in this.cacheMap;
    invariant this.cacheMap[lfuKey].1 == minFreq;
    invariant forall e :: e in seenItems ==> minFreq <= e.1.1;
    invariant forall e :: e in seenItems ==> minFreq <= this.cacheMap[e.0].1;
    invariant forall e :: e in seenItems ==> this.cacheMap[lfuKey].1 <= this.cacheMap[e.0].1;
    invariant exists e :: e in seenItems + items ==> minFreq == e.1.1;
    {
    var item :| item in items;

    if (item.1.1 < minFreq) {
      lfuKey := item.0;
      minFreq := item.1.1;
    }
    items := items - { item };
    seenItems := seenItems + { item };
    }
    assert seenItems == this.cacheMap.Items;
    assert this.cacheMap[lfuKey].1 == minFreq;
    assert forall e :: e in seenItems ==> minFreq <= e.1.1;
    assert forall e :: e in this.cacheMap.Items ==> minFreq <= e.1.1;
    assert forall k :: k in seenItems ==> this.cacheMap[lfuKey].1 <= this.cacheMap[k.0].1;
    assert forall k :: k in this.cacheMap.Items ==> this.cacheMap[lfuKey].1 <= this.cacheMap[k.0].1;
    // assert forall k :: k in cacheMap ==> cacheMap[lfuKey].1 <= cacheMap[k].1; // ????
    return lfuKey;
  }

  method get(key: int) returns (value: int)
    requires this.Valid();
    modifies this;
    ensures this.Valid();
    ensures key !in this.cacheMap ==> value == -1;
    ensures forall e :: e in old(this.cacheMap) <==> e in this.cacheMap;
    ensures forall e :: e in old(this.cacheMap) ==> (old(this.cacheMap[e].0) == this.cacheMap[e].0);
    ensures key in this.cacheMap ==> value == this.cacheMap[key].0 && old(this.cacheMap[key].1) == this.cacheMap[key].1-1;
  {
    assert key in this.cacheMap ==> this.cacheMap[key].0 >= 0;
    if(key !in this.cacheMap) {
    value := -1;
    }
    else{
    assert key in this.cacheMap;
    assert this.cacheMap[key].0 >= 0;
    value := this.cacheMap[key].0;
    var oldFreq := this.cacheMap[key].1;
    var newV := (value, oldFreq + 1);
    this.cacheMap := this.cacheMap[key := newV];
    }
    print "after get: ";
    print this.cacheMap;
    print "\n";
    return value;
  }
  
  
   method put(key: int, value: int)
    requires this.Valid();
    requires value > 0;
    modifies this
    ensures this.Valid();
     
   {
    if (key in this.cacheMap) {
      var currFreq := this.cacheMap[key].1;
      this.cacheMap := this.cacheMap[key := (value, currFreq)];
    } else {
      if (|this.cacheMap| < this.capacity) {
      this.cacheMap := this.cacheMap[key := (value, 1)];
      } else {
      var LFUKey := this.getLFUKey();
      assert LFUKey in this.cacheMap;
      assert |this.cacheMap| == this.capacity;
      ghost var oldMap := this.cacheMap;
      var newMap := this.cacheMap - {LFUKey};
      this.cacheMap := newMap;
      assert newMap == this.cacheMap - {LFUKey};
      assert LFUKey !in this.cacheMap;
      assert LFUKey in oldMap;
      ghost var oldCard := |oldMap|;
      ghost var newCard := |newMap|;
      assert |this.cacheMap.Keys| < |oldMap|; // ????
      this.cacheMap := this.cacheMap[key := (value, 1)];
      }
    }
    print "after put: ";
    print this.cacheMap;
    print "\n";
   }
 }

 method Main()
 {
   var lfuCache := new LFUCache(5);
   print "Cache Capacity = 5 \n";
   print "PUT (1, 1) - ";
   lfuCache.put(1,1);
   print "PUT (2, 2) - ";
   lfuCache.put(2,2);
   print "PUT (3, 3) - ";
   lfuCache.put(3,3);
   print "GET (1) - ";
   var val := lfuCache.get(1);
   print "get(1) = ";
   print val;
   print "\n";
   print "PUT (3, 5) - ";
   lfuCache.put(3,5);
   print "GET (3) - ";
   val := lfuCache.get(3);
   print "get(3) = ";
   print val;
   print "\n";
   print "PUT (4, 6) - ";
   lfuCache.put(4,6);
   print "PUT (5, 7) - ";
   lfuCache.put(5,7);
   print "PUT (10, 100) - ";
   lfuCache.put(10,100);
   print "GET (2) - ";
   val := lfuCache.get(2);
   print "get(2) = ";
   print val;
   print "\n";
 }
