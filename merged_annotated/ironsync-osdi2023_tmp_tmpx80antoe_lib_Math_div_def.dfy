// ironsync-osdi2023_tmp_tmpx80antoe_lib_Math_div_def.dfy


module Math__div_def_i {
  function div(x: int, d: int): int
    requires d != 0
  {
    x / d
  }
  // pure-end

  function mod(x: int, d: int): int
    requires d != 0
  {
    x % d
  }
  // pure-end

  function div_recursive(x: int, d: int): int
    requires d != 0
  {
    INTERNAL_div_recursive(x, d)
  }
  // pure-end

  function mod_recursive(x: int, d: int): int
    requires d > 0
  {
    INTERNAL_mod_recursive(x, d)
  }
  // pure-end

  function mod_boogie(x: int, y: int): int
    requires y != 0
  {
    x % y
  }
  // pure-end

  function div_boogie(x: int, y: int): int
    requires y != 0
  {
    x / y
  }
  // pure-end

  function my_div_recursive(x: int, d: int): int
    requires d != 0
  {
    if d > 0 then
      my_div_pos(x, d)
    else
      -1 * my_div_pos(x, -1 * d)
  }
  // pure-end

  function my_div_pos(x: int, d: int): int
    requires d > 0
    decreases if x < 0 then d - x else x
  {
    if x < 0 then
      -1 + my_div_pos(x + d, d)
    else if x < d then
      0
    else
      1 + my_div_pos(x - d, d)
  }
  // pure-end

  function my_mod_recursive(x: int, m: int): int
    requires m > 0
    decreases if x < 0 then m - x else x
  {
    if x < 0 then
      my_mod_recursive(m + x, m)
    else if x < m then
      x
    else
      my_mod_recursive(x - m, m)
  }
  // pure-end

  function INTERNAL_mod_recursive(x: int, m: int): int
    requires m > 0
  {
    my_mod_recursive(x, m)
  }
  // pure-end

  function INTERNAL_div_recursive(x: int, d: int): int
    requires d != 0
  {
    my_div_recursive(x, d)
  }
  // pure-end
}
