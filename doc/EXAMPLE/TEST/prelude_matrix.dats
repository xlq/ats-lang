(*
** some testing code for functions declared in
** prelude/SATS/matrix.sats
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Spring, 2009
//

(* ****** ****** *)

// staload "prelude/SATS/matrix.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list_vt.dats"
staload _(*anonymous*) = "prelude/DATS/matrix.dats"

(* ****** ****** *)

implement main (argc, argv) = let
  val () = () where {
    #define row 2
    #define col 5
    val M = matrix_make_arraysize {int}
      (row, col) ($arrsz (0, 1, 2, 3, 4, 5, 6, 7, 8, 9))
    prval pf = unit_v ()
    // testing [matrix_iforeach_fun]
    val () = print "M (0-9) =\n"
    val () = matrix_iforeach_fun {unit_v} (pf | M, f, row, col) where {
      fn f (
          pf: !unit_v | i: sizeLt row, j: sizeLt col, x: &int
        ) :<> void = $effmask_all let
        val () = if i+j > 0 then (if j = 0 then print "\n" else print ", ") in
        print x
      end // end of [f]
    } // end of [val]
    val () = print_newline ()
    // testing [matrix_iforeach_clo]
    val () = print "M (0-9) =\n"
    val () = matrix_iforeach_clo {unit_v} (pf | M, !p_f, row, col) where {
      var !p_f = @lam
        (pf: !unit_v | i: sizeLt row, j: sizeLt col, x: &int): void =<clo>
        $effmask_all (let
          val () = if i+j > 0 then (if j = 0 then print "\n" else print ", ") in
          print x
        end) // end of [$effmask_all]
    } // end of [val]
    val () = print_newline ()
    prval unit_v () = pf
  } // end of [val]
in
  print "The run of [prelude_matrix.dats] is done successfully!\n"
end // end of [main]

(* ****** ****** *)

(* end of [prelude_matrix.dats] *)
