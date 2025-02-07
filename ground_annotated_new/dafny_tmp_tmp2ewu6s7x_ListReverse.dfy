function reverse(xs: seq<nat>): seq<nat>
{
  if xs == [] then
    []
  else
    reverse(xs[1..]) + [xs[0]]
}
// pure-end

lemma ReverseAppendDistr(xs: seq<nat>, ys: seq<nat>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
  // post-conditions-end
{
// impl-start
  if {
    case xs == [] =>
      calc {
        reverse([] + ys);
        calc {
          [] + ys;
          ys;
        }
        reverse(ys);
        reverse(ys) + reverse([]);
      }
    case xs != [] =>
      {
        var zs := xs + ys;
        assert zs[1..] == xs[1..] + ys;
      }
  }
// impl-end
}

lemma ReverseInvolution(xxs: seq<nat>)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures reverse(reverse(xxs)) == xxs
  // post-conditions-end
{
// impl-start
  if {
    case xxs == [] =>
      {
      }
    case xxs != [] =>
      calc {
        reverse(reverse(xxs));
      ==
        reverse(reverse(xxs[1..]) + [xxs[0]]);
      ==
        {
          ReverseAppendDistr(reverse(xxs[1..]), [xxs[0]]);
        }
        reverse([xxs[0]]) + reverse(reverse(xxs[1..]));
      ==
        {
          ReverseInvolution(xxs[1..]);
        }
        calc {
          reverse([xxs[0]]);
        ==
          [] + [xxs[0]];
        ==
          [xxs[0]];
        }
        [xxs[0]] + xxs[1..];
      ==
        xxs;
      }
  }
// impl-end
}
