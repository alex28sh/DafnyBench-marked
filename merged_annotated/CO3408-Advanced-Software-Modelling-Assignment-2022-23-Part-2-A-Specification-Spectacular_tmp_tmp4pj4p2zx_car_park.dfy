// CO3408-Advanced-Software-Modelling-Assignment-2022-23-Part-2-A-Specification-Spectacular_tmp_tmp4pj4p2zx_car_park.dfy

method Main()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var carPark := new CarPark();
  var availableSpaces := carPark.checkAvailability();
  // assert-start
  assert availableSpaces == 2;
  // assert-end

  var success := carPark.enterCarPark("car1");
  availableSpaces := carPark.checkAvailability();
  // assert-start
  assert success && carPark.carPark == {"car1"} && availableSpaces == 1;
  // assert-end

  success := carPark.enterCarPark("car2");
  availableSpaces := carPark.checkAvailability();
  // assert-start
  assert success && "car2" in carPark.carPark && carPark.carPark == {"car1", "car2"} && availableSpaces == 0;
  // assert-end

  success := carPark.enterCarPark("car3");
  // assert-start
  assert !success && carPark.carPark == {"car1", "car2"} && carPark.reservedCarPark == {};
  // assert-end

  success := carPark.makeSubscription("car4");
  // assert-start
  assert success && carPark.subscriptions == {"car4"};
  // assert-end

  success := carPark.enterReservedCarPark("car4");
  // assert-start
  assert success && carPark.reservedCarPark == {"car4"};
  // assert-end

  success := carPark.enterReservedCarPark("car5");
  // assert-start
  assert !success && carPark.reservedCarPark == {"car4"};
  // assert-end

  success := carPark.makeSubscription("car6");
  // assert-start
  assert success && carPark.subscriptions == {"car4", "car6"};
  // assert-end

  success := carPark.makeSubscription("car7");
  // assert-start
  assert success && carPark.subscriptions == {"car4", "car6", "car7"};
  // assert-end

  success := carPark.makeSubscription("car8");
  // assert-start
  assert !success && carPark.subscriptions == {"car4", "car6", "car7"};
  // assert-end

  success := carPark.enterReservedCarPark("car6");
  // assert-start
  assert success && carPark.reservedCarPark == {"car4", "car6"};
  // assert-end

  success := carPark.enterReservedCarPark("car7");
  // assert-start
  assert success && carPark.reservedCarPark == {"car4", "car6", "car7"};
  // assert-end

  // assert-start
  assert carPark.carPark == {"car1", "car2"};
  // assert-end

  success := carPark.leaveCarPark("car1");
  // assert-start
  assert success && carPark.carPark == {"car2"} && carPark.reservedCarPark == {"car4", "car6", "car7"};
  // assert-end

  // assert-start
  assert "car9" !in carPark.carPark && "car9" !in carPark.reservedCarPark;
  // assert-end

  success := carPark.leaveCarPark("car9");
  // assert-start
  assert !success && carPark.carPark == {"car2"} && carPark.reservedCarPark == {"car4", "car6", "car7"};
  // assert-end

  success := carPark.leaveCarPark("car6");
  // assert-start
  assert success && carPark.carPark == {"car2"} && carPark.reservedCarPark == {"car4", "car7"};
  // assert-end

  carPark.closeCarPark();
  // assert-start
  assert carPark.carPark == {} && carPark.reservedCarPark == {} && carPark.subscriptions == {};
  // assert-end

// impl-end
}

method MainB()
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  // post-conditions-end
{
// impl-start
  var carPark := new CarPark();
  // assert-start
  assert carPark.weekend == false;
  // assert-end

  carPark.openReservedArea();
  // assert-start
  assert carPark.weekend == true;
  // assert-end

  var success := carPark.enterReservedCarPark("car3");
  // assert-start
  assert "car3" !in carPark.subscriptions && success && carPark.carPark == {} && carPark.reservedCarPark == {"car3"};
  // assert-end

  carPark.closeCarPark();
  // assert-start
  assert carPark.carPark == {} && carPark.reservedCarPark == {} && carPark.subscriptions == {};
  // assert-end

// impl-end
}

class {:autocontracts} CarPark {
  const totalSpaces: nat := 10
  const normalSpaces: nat := 7
  const reservedSpaces: nat := 3
  const badParkingBuffer: int := 5
  var weekend: bool
  var subscriptions: set<string>
  var carPark: set<string>
  var reservedCarPark: set<string>

  constructor ()
    // pre-conditions-start
    requires true
    // pre-conditions-end
    // post-conditions-start
    ensures this.subscriptions == {} && this.carPark == {} && this.reservedCarPark == {} && this.weekend == false
    // post-conditions-end
  {
  // impl-start
    this.subscriptions := {};
    this.carPark := {};
    this.reservedCarPark := {};
    this.weekend := false;
  // impl-end
  }

  ghost predicate Valid()
    reads this
  {
    this.carPark * this.reservedCarPark == {} &&
    |this.carPark| <= this.totalSpaces + this.badParkingBuffer &&
    this.normalSpaces + this.reservedSpaces == this.totalSpaces &&
    |this.reservedCarPark| <= this.reservedSpaces
  }
  // pure-end

  method leaveCarPark(car: string) returns (success: bool)
    // pre-conditions-start
    requires true
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures success ==> (car in old(this.carPark) && this.carPark == old(this.carPark) - {car} && this.reservedCarPark == old(this.reservedCarPark)) || (car in old(this.reservedCarPark) && this.reservedCarPark == old(this.reservedCarPark) - {car} && this.carPark == old(this.carPark))
    ensures success ==> car !in this.carPark && car !in this.reservedCarPark
    ensures !success ==> this.carPark == old(this.carPark) && this.reservedCarPark == old(this.reservedCarPark) && car !in old(this.carPark) && car !in old(this.reservedCarPark)
    ensures this.subscriptions == old(this.subscriptions) && this.weekend == old(this.weekend)
    // post-conditions-end
  {
  // impl-start
    success := false;
    if car in this.carPark {
      this.carPark := this.carPark - {car};
      success := true;
    } else if car in this.reservedCarPark {
      this.reservedCarPark := this.reservedCarPark - {car};
      success := true;
    }
  // impl-end
  }

  method checkAvailability() returns (availableSpaces: int)
    // pre-conditions-start
    requires true
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.weekend ==> availableSpaces == this.normalSpaces - old(|this.carPark|) + (this.reservedSpaces - old(|this.reservedCarPark|)) - this.badParkingBuffer
    ensures !this.weekend ==> availableSpaces == this.normalSpaces - old(|this.carPark|) - this.badParkingBuffer
    ensures this.carPark == old(this.carPark) && this.reservedCarPark == old(this.reservedCarPark) && this.weekend == old(this.weekend) && this.subscriptions == old(this.subscriptions)
    // post-conditions-end
  {
  // impl-start
    if this.weekend {
      availableSpaces := this.normalSpaces - |this.carPark| + (this.reservedSpaces - |this.reservedCarPark|) - this.badParkingBuffer;
    } else {
      availableSpaces := this.normalSpaces - |this.carPark| - this.badParkingBuffer;
    }
  // impl-end
  }

  method makeSubscription(car: string) returns (success: bool)
    // pre-conditions-start
    requires true
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures success ==> old(|this.subscriptions|) < this.reservedSpaces && car !in old(this.subscriptions) && this.subscriptions == old(this.subscriptions) + {car}
    ensures !success ==> this.subscriptions == old(this.subscriptions) && (car in old(this.subscriptions) || old(|this.subscriptions|) >= this.reservedSpaces)
    ensures this.carPark == old(this.carPark) && this.reservedCarPark == old(this.reservedCarPark) && this.weekend == old(this.weekend)
    // post-conditions-end
  {
  // impl-start
    if |this.subscriptions| >= this.reservedSpaces || car in this.subscriptions {
      success := false;
    } else {
      this.subscriptions := this.subscriptions + {car};
      success := true;
    }
  // impl-end
  }

  method openReservedArea()
    // pre-conditions-start
    requires true
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.carPark == old(this.carPark) && this.reservedCarPark == old(this.reservedCarPark) && this.weekend == true && this.subscriptions == old(this.subscriptions)
    // post-conditions-end
  {
  // impl-start
    this.weekend := true;
  // impl-end
  }

  method closeCarPark()
    // pre-conditions-start
    requires true
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures this.carPark == {} && this.reservedCarPark == {} && this.subscriptions == {}
    ensures this.weekend == old(this.weekend)
    // post-conditions-end
  {
  // impl-start
    this.carPark := {};
    this.reservedCarPark := {};
    this.subscriptions := {};
  // impl-end
  }

  method enterCarPark(car: string) returns (success: bool)
    // pre-conditions-start
    requires true
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures success ==> car !in old(this.carPark) && car !in old(this.reservedCarPark) && old(|this.carPark|) < this.normalSpaces - this.badParkingBuffer
    ensures success ==> this.carPark == old(this.carPark) + {car}
    ensures !success ==> this.carPark == old(this.carPark) && this.reservedCarPark == old(this.reservedCarPark)
    ensures !success ==> car in old(this.carPark) || car in old(this.reservedCarPark) || old(|this.carPark|) >= this.normalSpaces - this.badParkingBuffer
    ensures this.subscriptions == old(this.subscriptions) && this.reservedCarPark == old(this.reservedCarPark) && this.weekend == old(this.weekend)
    // post-conditions-end
  {
  // impl-start
    if |this.carPark| >= this.normalSpaces - this.badParkingBuffer || car in this.carPark || car in this.reservedCarPark {
      return false;
    } else {
      this.carPark := this.carPark + {car};
      return true;
    }
  // impl-end
  }

  method enterReservedCarPark(car: string) returns (success: bool)
    // pre-conditions-start
    requires true
    // pre-conditions-end
    // post-conditions-start
    modifies this
    ensures success ==> car !in old(this.carPark) && car !in old(this.reservedCarPark) && old(|this.reservedCarPark|) < this.reservedSpaces && (car in this.subscriptions || this.weekend == true)
    ensures success ==> this.reservedCarPark == old(this.reservedCarPark) + {car}
    ensures !success ==> this.carPark == old(this.carPark) && this.reservedCarPark == old(this.reservedCarPark)
    ensures !success ==> car in old(this.carPark) || car in old(this.reservedCarPark) || old(|this.reservedCarPark|) >= this.reservedSpaces || (car !in this.subscriptions && this.weekend == false)
    ensures this.subscriptions == old(this.subscriptions) && this.carPark == old(this.carPark) && this.weekend == old(this.weekend)
    ensures this.weekend == old(this.weekend) && this.subscriptions == old(this.subscriptions)
    // post-conditions-end
  {
  // impl-start
    if |this.reservedCarPark| >= this.reservedSpaces || car in this.carPark || car in this.reservedCarPark || (car !in this.subscriptions && this.weekend == false) {
      return false;
    } else {
      this.reservedCarPark := this.reservedCarPark + {car};
      return true;
    }
  // impl-end
  }
}
