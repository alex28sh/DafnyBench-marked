// DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy

ghost predicate prime(n: nat)
{
  n > 1 &&
  forall nr | 1 < nr < n :: 
    n % nr != 0
}
// pure-end

method testingMethod()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  // assert-start
  assert !(forall nr | 1 < nr < 15 :: 15 % nr != 0) ==> exists nr | 1 < nr < 15 :: 15 % nr == 0;
  // assert-end

  // assert-start
  assert 15 % 3 == 0;
  // assert-end

  // assert-start
  assert exists nr | 1 < nr < 15 :: 15 % nr == 0;
  // assert-end

  var pm := new PrimeMap();
  pm.InsertPrime(13);
  pm.InsertNumber(17);
  pm.InsertNumber(15);
  // assert-start
  assert pm.database.Keys == {17, 15, 13};
  // assert-end

  var result: Answer := pm.IsPrime?(17);
  // assert-start
  assert result == Yes;
  // assert-end

  var result2: Answer := pm.IsPrime?(15);
  // assert-start
  assert result2 == No;
  // assert-end

  var result3: Answer := pm.IsPrime?(454);
  // assert-start
  assert result3 == Unknown;
  // assert-end

  var result4: Answer := pm.IsPrime?(13);
  // assert-start
  assert result4 == Yes;
  // assert-end

// impl-end
}

datatype Answer = Yes | No | Unknown

class {:autocontracts} PrimeMap {
  var database: map<nat, bool>

  ghost predicate Valid()
    reads this
  {
    forall i | i in this.database.Keys :: 
      this.database[i] == true <==> prime(i)
  }
  // pure-end

  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.database == map[]
    // post-conditions-end
  {
  // impl-start
    this.database := map[];
  // impl-end
  }

  method InsertPrime(n: nat)
    // pre-conditions-start
    requires prime(n)
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.database.Keys == old(this.database.Keys) + {n}
    ensures this.database == this.database[n := true]
    // post-conditions-end
  {
  // impl-start
    this.database := this.database[n := true];
  // impl-end
  }

  method InsertNumber(n: nat)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.database.Keys == old(this.database.Keys) + {n}
    ensures prime(n) <==> this.database == this.database[n := true]
    ensures !prime(n) <==> this.database == this.database[n := false]
    // post-conditions-end
  {
  // impl-start
    var prime: bool;
    prime := this.testPrimeness(n);
    this.database := this.database[n := prime];
  // impl-end
  }

  method IsPrime?(n: nat) returns (answer: Answer)
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    ensures this.database.Keys == old(this.database.Keys)
    ensures n in this.database && prime(n) <==> answer == Yes
    ensures n in this.database && !prime(n) <==> answer == No
    ensures !(n in this.database) <==> answer == Unknown
    // post-conditions-end
  {
  // impl-start
    if !(n in this.database) {
      return Unknown;
    } else if this.database[n] == true {
      return Yes;
    } else if this.database[n] == false {
      return No;
    }
  // impl-end
  }

  method testPrimeness(n: nat) returns (result: bool)
    // pre-conditions-start
    requires n >= 0
    // pre-conditions-end
    // post-conditions-start
    ensures result <==> prime(n)
    // post-conditions-end
  {
  // impl-start
    if n == 0 || n == 1 {
      return false;
    }
    var i := 2;
    result := true;
    while i < n
      // invariants-start

      invariant i >= 2 && i <= n
      invariant result <==> forall j | 1 < j <= i - 1 :: n % j != 0
      // invariants-end

    {
      if n % i == 0 {
        result := false;
      }
      i := i + 1;
    }
  // impl-end
  }
}
