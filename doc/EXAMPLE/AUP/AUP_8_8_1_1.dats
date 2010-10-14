//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October, 2010
//
(* ****** ****** *)
//
// book: AUP (2nd edition), pages 578 - 585
// section 8.8.1: Host Functions
//
(* ****** ****** *)

staload "prelude/SATS/ptrarr.sats"
staload UNSAFE = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "libc/SATS/errno.sats"
staload "libc/SATS/netdb.sats"
staload "libc/SATS/string.sats"
staload "libc/sys/SATS/sockaddr.sats"
staload "libc/arpa/SATS/inet.sats"

(* ****** ****** *)

fun display_hostent
  (h: &hostent): void = let
  val (fpf_name | name) = hostent_get_name (h)
  val () = printf (
    "name: %s; type: %d; len: %d\n"
  , @($UNSAFE.vtcast{string} (name), h.h_addrtype, h.h_length)
  ) // end of [printf]
  prval () = fpf_name (name)
//
  val (pf, fpf | p) = hostent_get_aliases (h)
  val n = ptrarr_size (!p)
  prval (pf1 , fpf1) = ptrarr_takeout{string} (pf)
  val () = loop (!p, n, 0) where {
    fun loop {n,i:nat | i <= n} .<n-i>.
      (A: &(@[string][n]), n: size_t n, i: size_t i): void =
      if i < n then let
        val () = printf ("\t%s\n", @(A.[i])) in loop (A, n, i+1)
      end else () // end of [loop]
    // end of [loop]
  } // end of [val]
  prval () = pf := fpf1 (pf1)
  prval () = fpf (pf)
//
  val () = if (h.h_addrtype = $UNSAFE.cast2int(AF_INET)) then let
//
  val (pf, fpf | p) = hostent_get_addr_list (h)
  val n = ptrarr_size (!p)
  typedef Ptr1 = $PA.Ptr1
  prval (pf1 , fpf1) = ptrarr_takeout{Ptr1} (pf)
  val () = loop (!p, n, 0) where {
    fun loop {n,i:nat | i <= n} .<n-i>.
      (A: &(@[Ptr1][n]), n: size_t n, i: size_t i): void =
      if i < n then let
        val [l:addr] pi = A.[i]
        prval pfi = $UNSAFE.vcast{in_addr_struct @ l} (unit_v)
        val (fpf_addr | addr) = inet_ntoa (!pi)
        prval () = $UNSAFE.vcast2void (pfi)
        val () = printf ("\t%s\n", @($UNSAFE.vtcast{string}(addr)))
        prval () = fpf_addr (addr)
      in
        loop (A, n, i+1)
      end else () // end of [loop]
    // end of [loop]
  } // end of [val]
  prval () = pf := fpf1 (pf1)
  prval () = fpf (pf)    
//
  in
    // nothing
  end // end of [val]
//
in
end // end of [display_hostent]

(* ****** ****** *)

fun hostdb (): void = let
  val (pf | ()) = sethostent (true)
  val () = while (true) let
    val (pf, fpf | p) = gethostent (pf | (*none*))
  in
    if p > null then let
      val () = display_hostent (!p); prval () = fpf (pf)
    in
      continue
    end else let
      prval () = fpf (pf) in break
    end // end of [if]
  end // end of [while]
  val () = endhostent (pf | (*none*))
in
  // nothing
end // end of [hostdb]

(* ****** ****** *)

implement
main () = () where {
//
  val () = hostdb ()
//
} // end of [main]

(* ****** ****** *)

(* end of [AUP_8_8_1_1.dats] *)
