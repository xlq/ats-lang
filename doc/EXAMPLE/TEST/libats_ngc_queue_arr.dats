(*
//
// Author: Hongwei Xi (March, 2010)
//
*)

(* ****** ****** *)

staload RAND = "libc/SATS/random.sats"

(* ****** ****** *)

staload Q = "libats/ngc/SATS/queue_arr.sats"
stadef QUEUE = $Q.QUEUE
stadef QUEUE0 = $Q.QUEUE0

staload _(*anon*) = "libats/ngc/DATS/queue_arr.dats"

(* ****** ****** *)

// dynload "libats/DATS/linqueue_arr.dats" // not needed as [ATS_DYNLOADFLAG = 0]

(* ****** ****** *)

#define CAP 2000000
#define N1 1500000; #define N2 1000000

(* ****** ****** *)

implement main () = () where {
  typedef itm = int
  var q: QUEUE0 (itm)
  val (pfgc, pfarr | parr) = array_ptr_alloc<itm> (CAP)
  val () = $Q.queue_initialize<itm> (pfgc, pfarr | q, CAP, parr)
//
  val () = loop (q, N1, 0) where {
    fun loop {i,j:nat | i+j <= CAP} .<i>.
      (q: &QUEUE (itm, CAP, j) >> QUEUE (itm, CAP, i+j), i: int i, j: int j): void =
      if i > 0 then let
        val () = $Q.queue_insert<itm> (q, j) in loop (q, i-1, j+1)
      end // end of [val]
    // end of [loop]
  } // end of [val]
//
  val () = loop (q, 0) where {
    fun loop {i:nat | i <= N2} .<N2-i>.
      (q: &QUEUE (itm, CAP, N1-i) >> QUEUE (itm, CAP, N1-N2), i: int i): void =
      if i < N2 then let
        val x = $Q.queue_remove<itm> (q)
        val () = assert_errmsg (x = i, #LOCATION)
      in
        loop (q, i+1)
      end // end of [val]
    // end of [loop]
  } // end of [val]
//
  val () = loop (q, N2, N1) where {
    fun loop {i,j:nat | i <= N2} .<i>.
      (q: &QUEUE (itm, CAP, N1-i) >> QUEUE (itm, CAP, N1), i: int i, j: int j): void =
      if i > 0 then let
        val () = $Q.queue_insert<itm> (q, j) in loop (q, i-1, j+1)
      end // end of [val]
    // end of [loop]
  } // end of [val]
//
  val () = loop (q, 0) where {
    fun loop {i:nat | i <= N1} .<N1-i>.
      (q: &QUEUE (itm, CAP, N1-i) >> QUEUE (itm, CAP, 0), i: int i): void =
      if i < N1 then let
        val x = $Q.queue_remove<itm> (q)
        val () = assert_errmsg (x = N2+i, #LOCATION)
      in
        loop (q, i+1)
      end // end of [val]
    // end of [loop]
  } // end of [val]
//
  val (pfgc, pfarr | parr) = $Q.queue_uninitialize_vt {itm} (q)
  val () = array_ptr_free (pfgc, pfarr | parr)
//
  val () = print "[libats_linqueue_arr.dats] testing passes!\n"
//
} // end of [main]

(* ****** ****** *)

(* end of [libats_linqueue_arr.dats] *)
