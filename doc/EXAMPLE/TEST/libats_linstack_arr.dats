(*
//
// Author: Hongwei Xi (March, 2010)
//
*)

(* ****** ****** *)

staload RAND = "libc/SATS/random.sats"

(* ****** ****** *)

staload _(*anon*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

staload Q = "libats/SATS/linstack_arr.sats"
stadef STACK = $Q.STACK
stadef STACK0 = $Q.STACK0

staload _(*anon*) = "libats/DATS/linstack_arr.dats"

(* ****** ****** *)

// dynload "libats/DATS/linstack_arr.dats" // not needed as [ATS_DYNLOADFLAG = 0]

(* ****** ****** *)

#define N 2000000

(* ****** ****** *)

implement main () = () where {
  typedef itm = int
  var q: STACK0 (itm)
  val () = $Q.stack_initialize<itm> (q, N)
//
  val () = loop (q, N, 0) where {
    fun loop {i,j:nat | i+j <= N} .<i>.
      (q: &STACK (itm, N, j) >> STACK (itm, N, i+j), i: int i, j: int j): void =
      if i > 0 then let
        val () = $Q.stack_insert<itm> (q, j) in loop (q, i-1, j+1)
      end // end of [val]
    // end of [loop]
  } // end of [val]
//
  val () = loop (q, 0) where {
    fun loop {i:nat | i <= N} .<N-i>.
      (q: &STACK (itm, N, N-i) >> STACK (itm, N, 0), i: int i): void =
      if i < N then let
        val x = $Q.stack_remove<itm> (q)
        val () = assert_errmsg (x = N-1-i, #LOCATION)
      in
        loop (q, i+1)
      end // end of [val]
    // end of [loop]
  } // end of [val]
//
  val () = $Q.stack_uninitialize_vt {itm} (q)
//
  val () = print "[libats_linstack_arr.dats] testing passes!\n"
//
} // end of [main]

(* ****** ****** *)

(* end of [libats_linstack_arr.dats] *)
