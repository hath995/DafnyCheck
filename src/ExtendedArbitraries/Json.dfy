include "../Arbitrary.dfy"
include "../utils.dfy"

// Best-effort JSON value arbitrary. Produces a depth-1 JSON document: a number,
// a quoted alphanumeric string, a boolean/null literal, a small array, or a
// single-field object. Implemented without Mix/FlatMap (Mix's disjointness
// precondition is unsatisfiable for non-empty repr sets, and FlatMap relies on
// the not-yet-proven recursion) by generating every component and selecting the
// rendering in a Map.
module ExtJson {
  import opened Arbitrary
  import opened LTLUtils

  const ALNUM: seq<char> :=
    ['a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z',
     '0','1','2','3','4','5','6','7','8','9']

  function RenderJson(sel: nat, num: nat, str: seq<char>, b: nat): string {
    if sel == 0 then IntToString(num)
    else if sel == 1 then "\"" + str + "\""
    else if sel == 2 then (if b == 0 then "true" else if b == 1 then "false" else "null")
    else if sel == 3 then "[" + IntToString(num) + "," + IntToString(b) + "]"
    else "{\"k\":" + IntToString(num) + "}"
  }

  method Json() returns (p: Arbitrary<string>)
    ensures p.Valid()
  {
    var sel := Arbitrary<nat>.Nats(5);
    var num := Arbitrary<nat>.Nats(100000);
    var alnum := Arbitrary<char>.Of(ALNUM);
    var str := Arbitrary<seq<char>>.Lists(alnum, 0, 8);
    var boolSel := Arbitrary<nat>.Nats(3);
    var combo := Arbitrary<nat>.Tuple4<nat, nat, seq<char>, nat>(sel, num, str, boolSel);
    p := combo.Map((t: (nat, nat, seq<char>, nat)) => RenderJson(t.0, t.1, t.2, t.3));
  }
}
