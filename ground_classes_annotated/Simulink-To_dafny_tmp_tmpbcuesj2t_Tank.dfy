// Simulink-To_dafny_tmp_tmpbcuesj2t_Tank.dfy

method checkRegulation(tank: Tank)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  modifies tank.pipe
  ensures (tank.height > 10 && tank.pipe.v1 == OFF && tank.pipe.v3 == ON && tank.pipe.v2 == old(tank.pipe.v2)) || (tank.height < 8 && tank.pipe.v1 == OFF && tank.pipe.v2 == ON && tank.pipe.v3 == old(tank.pipe.v3)) || ((tank.pipe.in_flowv3 > 5 || tank.pipe.in_flowv1 > 5) && tank.pipe.v2 == OFF && tank.pipe.v3 == old(tank.pipe.v3) && tank.pipe.v1 == old(tank.pipe.v1))
  // post-conditions-end
{
// impl-start
  if tank.height > 10 {
    tank.pipe.v1 := OFF;
    tank.pipe.v3 := ON;
    // assert-start
    assert tank.height > 10 && tank.pipe.v1 == OFF && tank.pipe.v3 == ON && tank.pipe.v2 == old(tank.pipe.v2);
    // assert-end

  } else if tank.height < 8 {
    tank.pipe.v1 := OFF;
    tank.pipe.v2 := ON;
    // assert-start
    assert tank.height < 8 && tank.pipe.v1 == OFF && tank.pipe.v2 == ON && tank.pipe.v3 == old(tank.pipe.v3);
    // assert-end

  }
  // assert-start
  assume (tank.pipe.in_flowv3 > 5 || tank.pipe.in_flowv1 > 5) && tank.pipe.v2 == OFF && tank.pipe.v3 == old(tank.pipe.v3) && tank.pipe.v1 == old(tank.pipe.v1);
  // assert-end

// impl-end
}

datatype Valve = ON | OFF

class Pipe {
  var v1: Valve
  var v2: Valve
  var v3: Valve
  var in_flowv1: int
  var in_flowv2: int
  var in_flowv3: int

  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    this.v1 := OFF;
    this.v2 := ON;
  // impl-end
  }
}

class Tank {
  var pipe: Pipe
  var height: int

  constructor ()
    // pre-conditions-start
    // pre-conditions-end
    // post-conditions-start
    // post-conditions-end
  {
  // impl-start
    pipe := new Pipe();
  // impl-end
  }
}
