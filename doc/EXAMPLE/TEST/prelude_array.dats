(*
** some testing code for functions declared in
** prelude/SATS/array.sats
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Spring, 2009
//

(* ****** ****** *)

// staload "prelude/SATS/array.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list_vt.dats"
staload _(*anonymous*) = "prelude/DATS/array.dats"

(* ****** ****** *)

implement
main (argc, argv) = let
  val () = () where {
    #define asz 10
    val A = array_make_arrsz {int}
      ($arrsz (0, 1, 2, 3, 4, 5, 6, 7, 8, 9))
    prval pf = unit_v ()
    // testing [array_iforeach_fun]
    val () = print "A (0-9) = "
    val () = array_iforeach_fun {unit_v} (pf | A, f, asz) where {
      fn f (
          pf: !unit_v | i: sizeLt asz, x: &int
        ) :<> void = $effmask_all let
        val () = if i > 0 then print ", " in print x
      end // end of [f]
    } // end of [val]
    val () = print_newline ()
    // testing [array_iforeach_clo]
    val () = print "A (0-9) = "
    val () = array_iforeach_clo {unit_v} (pf | A, !p_f, asz) where {
      var !p_f = @lam
        (pf: !unit_v | i: sizeLt asz, x: &int): void =<clo>
        $effmask_all (
          let val () = if i > 0 then print ", " in print x end
        ) // end of [$effmask_all]
    } // end of [val]
    val () = print_newline ()
    prval unit_v () = pf
  } // end of [val]
in
  print "The run of [prelude_array.dats] is done successfully!\n"
end // end of [main]

(* ****** ****** *)

(* end of [prelude_array.dats] *)
