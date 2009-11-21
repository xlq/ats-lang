//
//
// code demonstrating some typical uses of looping constructs
//
//

(* ****** ****** *)

fn fact (n: int): int = let
  var x: int = n
  var res: int = 1 // initialized
  val () = while (x > 0) (res := res * x; x := x - 1)
in
  res // res = n!
end // end of [fact]

(* ****** ****** *)

fn fact (n: int): int = let
  var x: int
  var res: int = 1 // initialized
  val () = for (x := 1 ; x <= n ; x := x+1) res := res * x
in
  res // res = n!
end // end of [fact]

(* ****** ****** *)

fn fact {n:nat} (n: int n): int = let
  var x: int
  var res: int = 1
(*
  // the loop invariant indicates that
  // the value of [x] is [n+1] at the point where the loop exits
*)
  val () = for* {i:nat | i <= n+1} .<n+1-i>.
    (x: int i): (x: int (n+1)) => (x := 0; x <= n ; x := x+1) res := res * x
  // end of [val]
in
  res
end // end of [fact]

(* ****** ****** *)

(* end of [looping.dats] *)
