//
// some testing code for functions declared in
// prelude/SATS/array.sats
//

(* ****** ****** *)

// staload "prelude/SATS/array0.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/array0.dats"

(* ****** ****** *)

implement main () = let
  val () = () where {
    #define asz 10
//
    val A = array0_make_arraysize {int}
      ($arrsz (0, 1, 2, 3, 4, 5, 6, 7, 8, 9))
//
    var i: int // uninitialized
    val () = for (i := 0; i < asz; i := i + 1) let
      val () = if i > 0 then print ", " in print A[i]
    end // end of [val]
    val () = print_newline ()
  } // end of [val]
  val () = () where {
    #define asz 10
//
    val A = array0_make_elt<int> (asz, 0)
//
    var i: int // uninitialized
    val () = for (i := 0; i < asz; i := i + 1) let
      val () = if i > 0 then print ", " in print A[i]
    end // end of [val]
    val () = print_newline ()
//
    val () = for (i := 0; i < asz; i := i + 1) (A[i] := i)
//
    val () = for (i := 0; i < asz; i := i + 1) let
      val () = if i > 0 then print ", " in print A[i]
    end // end of [val]
    val () = print_newline ()
  } // end of [val]
in
  print "The run of [prelude_array0.dats] is done successfully!\n"
end // end of [main]

(* ****** ****** *)

(* end of [prelude_array0.dats] *)


