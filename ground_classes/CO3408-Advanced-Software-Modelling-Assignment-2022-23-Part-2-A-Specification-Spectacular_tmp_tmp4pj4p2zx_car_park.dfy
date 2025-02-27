class {:autocontracts} CarPark {
  const totalSpaces: nat := 10;
  const normalSpaces: nat:= 7;
  const reservedSpaces: nat := 3;
  const badParkingBuffer: int := 5;

  var weekend: bool;
  var subscriptions: set<string>;
  var carPark: set<string>;
  var reservedCarPark: set<string>;

  constructor()
  requires true
  ensures this.subscriptions == {} && this.carPark == {} && this.reservedCarPark == {} && this.weekend == false;
  {
    this.subscriptions := {};
    this.carPark := {};
    this.reservedCarPark := {};
    this.weekend := false;
  }

  ghost predicate Valid()
  reads this
  {
    this.carPark * this.reservedCarPark == {} && |this.carPark| <= this.totalSpaces + this.badParkingBuffer && (this.normalSpaces + this.reservedSpaces) == this.totalSpaces && |this.reservedCarPark| <= this.reservedSpaces
  }

  method leaveCarPark(car: string) returns (success: bool)
  requires true
  modifies this
  ensures success ==> (((car in old(this.carPark)) && this.carPark == old(this.carPark) - {car} && this.reservedCarPark == old(this.reservedCarPark)) || ((car in old(this.reservedCarPark)) && this.reservedCarPark == old(this.reservedCarPark) - {car} && this.carPark == old(this.carPark)));
  ensures success ==> (car !in this.carPark) && (car !in this.reservedCarPark);
  ensures !success ==> this.carPark == old(this.carPark) && this.reservedCarPark == old(this.reservedCarPark) && (car !in old(this.carPark)) && (car !in old(this.reservedCarPark));
  ensures this.subscriptions == old(this.subscriptions) && this.weekend == old(this.weekend);
  {
    success := false;

    if car in this.carPark {
      this.carPark := this.carPark - {car};
      success := true;
    } else if car in this.reservedCarPark {
      this.reservedCarPark := this.reservedCarPark - {car};
      success := true;
    }
  }

  method checkAvailability() returns (availableSpaces: int)
  requires true
  modifies this
  ensures this.weekend ==> availableSpaces == (this.normalSpaces - old(|this.carPark|)) + (this.reservedSpaces - old(|this.reservedCarPark|)) - this.badParkingBuffer;
  ensures !this.weekend ==> availableSpaces == (this.normalSpaces - old(|this.carPark|)) - this.badParkingBuffer;
  ensures this.carPark == old(this.carPark) && this.reservedCarPark == old(this.reservedCarPark) && this.weekend == old(this.weekend) && this.subscriptions == old(this.subscriptions);
  {
    if (this.weekend){
      availableSpaces := (this.normalSpaces - |this.carPark|) + (this.reservedSpaces - |this.reservedCarPark|) - this.badParkingBuffer;
    } else{
      availableSpaces := (this.normalSpaces - |this.carPark|) - this.badParkingBuffer;
    }
  }

  method makeSubscription(car: string) returns (success: bool)
  requires true
  modifies this
  ensures success ==> old(|this.subscriptions|) < this.reservedSpaces && car !in old(this.subscriptions) && this.subscriptions == old(this.subscriptions) + {car};
  ensures !success ==> this.subscriptions == old(this.subscriptions) && (car in old(this.subscriptions) || old(|this.subscriptions|) >= this.reservedSpaces);
  ensures this.carPark == old(this.carPark) && this.reservedCarPark == old(this.reservedCarPark) && this.weekend == old(this.weekend);
  {
    if |this.subscriptions| >= this.reservedSpaces || car in this.subscriptions {
      success := false;
    } else {
      this.subscriptions := this.subscriptions + {car};
      success := true;
    }
  }

  method openReservedArea()
  requires true
  modifies this
  ensures this.carPark == old(this.carPark) && this.reservedCarPark == old(this.reservedCarPark) && this.weekend == true && this.subscriptions == old(this.subscriptions);
  {
    this.weekend := true;
  }

  method closeCarPark()
  requires true
  modifies this
  ensures this.carPark == {} && this.reservedCarPark == {} && this.subscriptions == {}
  ensures this.weekend == old(this.weekend);
  {
    this.carPark := {};
    this.reservedCarPark := {};
    this.subscriptions := {};
  }

  method enterCarPark(car: string) returns (success: bool)
  requires true
  modifies this
  ensures success ==> (car !in old(this.carPark)) && (car !in old(this.reservedCarPark)) && (old(|this.carPark|) < this.normalSpaces - this.badParkingBuffer);
  ensures success ==> this.carPark == old(this.carPark) + {car};
  ensures !success ==> this.carPark == old(this.carPark) && this.reservedCarPark == old(this.reservedCarPark);
  ensures !success ==> (car in old(this.carPark)) || (car in old(this.reservedCarPark) || (old(|this.carPark|) >= this.normalSpaces - this.badParkingBuffer));
  ensures this.subscriptions == old(this.subscriptions) && this.reservedCarPark == old(this.reservedCarPark) && this.weekend == old(this.weekend);
  {
    if (|this.carPark| >= this.normalSpaces - this.badParkingBuffer || car in this.carPark || car in this.reservedCarPark) {
      return false;
    }
    else
    {
      this.carPark := this.carPark + {car};
      return true;
    }
  }

  method enterReservedCarPark(car: string) returns (success: bool)
  requires true
  modifies this
  ensures success ==> (car !in old(this.carPark)) && (car !in old(this.reservedCarPark)) && (old(|this.reservedCarPark|) < this.reservedSpaces) && (car in this.subscriptions || this.weekend == true);
  ensures success ==> this.reservedCarPark == old(this.reservedCarPark) + {car};
  ensures !success ==> this.carPark == old(this.carPark) && this.reservedCarPark == old(this.reservedCarPark);
  ensures !success ==> (car in old(this.carPark)) || (car in old(this.reservedCarPark) || (old(|this.reservedCarPark|) >= this.reservedSpaces) || (car !in this.subscriptions && this.weekend == false));
  ensures this.subscriptions == old(this.subscriptions) && this.carPark == old(this.carPark) && this.weekend == old(this.weekend);
  ensures this.weekend == old(this.weekend) && this.subscriptions == old(this.subscriptions);
  {
    if (|this.reservedCarPark| >= this.reservedSpaces || car in this.carPark || car in this.reservedCarPark || (car !in this.subscriptions && this.weekend == false)) {
      return false;
    }
    else
    {
      this.reservedCarPark := this.reservedCarPark + {car};
      return true;
    }
  }
}

method Main() {
  // Initialises car park with 10 spaces, 3 of which are reserved and therefore 7 are normal
  var carPark := new CarPark();

  // As we are allowing 5 spaces for idiots who can't park within the lines 7 - 5 == 2
  var availableSpaces := carPark.checkAvailability();
  assert availableSpaces == 2;

  // Test entering the car park with one car, One space should now be left
  var success := carPark.enterCarPark("car1");
  availableSpaces := carPark.checkAvailability();
  assert success && carPark.carPark == {"car1"} && availableSpaces == 1;

  // Test entering the car with another car, No spaces should be left
  success := carPark.enterCarPark("car2");
  availableSpaces := carPark.checkAvailability();
  assert success && "car2" in carPark.carPark && carPark.carPark == {"car1", "car2"} && availableSpaces == 0;

  // Test entering with another car, should return invalid as carpark is full
  // normalSpaces = 7, minus 5 spaces because of the bad parking buffer, therefore 2 spaces max
  success := carPark.enterCarPark("car3");
  assert !success && carPark.carPark == {"car1", "car2"} && carPark.reservedCarPark == {};

  // Test creating car subscription
  success := carPark.makeSubscription("car4");
  assert success && carPark.subscriptions == {"car4"};

  // Test entering the reserved carPark with a valid and an invalid option
  success := carPark.enterReservedCarPark("car4");
  assert success && carPark.reservedCarPark == {"car4"};
  // This car doesn't have a subscription so it should not be successful
  success := carPark.enterReservedCarPark("car5");
  assert !success && carPark.reservedCarPark == {"car4"};

  // Test filling the car subscription list
  success := carPark.makeSubscription("car6");
  assert success && carPark.subscriptions == {"car4", "car6"};
  success := carPark.makeSubscription("car7");
  assert success && carPark.subscriptions == {"car4", "car6", "car7"};
  // This won't add as reserved spaces are 3 and we can't have more subscriptions than reserved spaces
  success := carPark.makeSubscription("car8");
  assert !success && carPark.subscriptions == {"car4", "car6", "car7"};

  // Test filling reserved car park
  success := carPark.enterReservedCarPark("car6");
  assert success && carPark.reservedCarPark == {"car4", "car6"};
  success := carPark.enterReservedCarPark("car7");
  assert success && carPark.reservedCarPark == {"car4", "car6", "car7"};

  // Test leaving car park
  assert carPark.carPark == {"car1", "car2"};
  success := carPark.leaveCarPark("car1");
  assert success && carPark.carPark == {"car2"} && carPark.reservedCarPark == {"car4", "car6", "car7"};

  // Test leaving with car that doesn't exist
  assert "car9" !in carPark.carPark && "car9" !in carPark.reservedCarPark;
  success := carPark.leaveCarPark("car9");
  assert !success && carPark.carPark == {"car2"} && carPark.reservedCarPark == {"car4", "car6", "car7"};

  // Test leaving reserved car park
  success := carPark.leaveCarPark("car6");
  assert success && carPark.carPark == {"car2"} && carPark.reservedCarPark == {"car4", "car7"};

  // Testing closing car park, all cars should be destroyed
  carPark.closeCarPark();
  assert carPark.carPark == {} && carPark.reservedCarPark == {} && carPark.subscriptions == {};
}

method MainB () {
  var carPark := new CarPark();

  assert carPark.weekend == false;
  carPark.openReservedArea();
  assert carPark.weekend == true;

  var success := carPark.enterReservedCarPark("car3");
  assert "car3" !in carPark.subscriptions && success && carPark.carPark == {} && carPark.reservedCarPark == {"car3"};

  carPark.closeCarPark();
  assert carPark.carPark == {} && carPark.reservedCarPark == {} && carPark.subscriptions == {};
}
