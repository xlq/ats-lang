(*
** some testing code for functions declared in
** prelude/SATS/matrix0.sats
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Summer, 2009
//

(* ****** ****** *)

// staload "prelude/SATS/matrix0.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/matrix0.dats"

(* ****** ****** *)

implement main () = let
  #define row 5; #define col 2; #define asz 10
  val () = () where {
    val (pf_mul | _(*asz*)) = op imul2 (row, col)
    prval () = mul_elim (pf_mul)
//
    val M = matrix0_make_arraysize {int} {row,col} {asz}
      (pf_mul | row, col, $arrsz (0, 1, 2, 3, 4, 5, 6, 7, 8, 9))
//
    var i: int and j: int // uninitialized
    val () = for* (j: int?) => (i := 0; i < row; i := i + 1) let
      val () = for (j := 0; j < col; j := j + 1) let
        val () = if j > 0 then print ", " in print M[i,j]
      end // end of [val]
      val () = print_newline ()
    in
      // nothing
    end // end of [val]
  } // end of [val]
  val () = () where {
    val M = matrix0_make_elt<int> (row, col, 0)
    var i: int and j: int // uninitialized
    val () = for*
      (j: int?) => (i := 0; i < row; i := i + 1) let
      val () = for (j := 0; j < col; j := j + 1) M[i,j] := i * col + j
    in
      // nothing
    end // end of [val]
    val () = loop1 (0) where {
      fun loop1 {i:nat | i <= row} 
        (i: int i):<cloref1> void = if i < row then loop2 (i, 0) else ()
      // end of [loop1]
      and loop2 {i,j:nat | i < row; j <= col}
        (i: int i, j: int j):<cloref1> void =
        if j < col then begin
          if j > 0 then print ", "; print M[i,j]; loop2 (i, j+1)
        end else begin
          print_newline (); loop1 (i+1) 
        end // end of [if]
      // end of [loop2]
    } // end of [val]
  } (* end of [val] *)
in
  print "The run of [prelude_matrix0.dats] is done successfully!\n"
end // end of [main]

(* ****** ****** *)

(* end of [prelude_matrix0.dats] *)
