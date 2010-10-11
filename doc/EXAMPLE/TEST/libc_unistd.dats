(*
** some testing code for functions declared in
** libc/SATS/stdlib.sats
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October, 2010
//

(* ****** ****** *)

staload "libc/SATS/stdio.sats"
staload "libc/SATS/unistd.sats"

(* ****** ****** *)

implement
main () = () where {
//
  var !p_buf with pf_buf = @[byte][128]()
  val (pfopt | err) = gethostname (pf_buf | p_buf, 128)
  val () = assertloc (err >= 0)
  prval gethostname_v_succ pf = pfopt
  val () = (print "gethostname() = "; print_strbuf (!p_buf); print_newline ())
  prval () = pf_buf := bytes_v_of_strbuf_v (pf)
//
  val err = sethostname ("xxx.yyy.zzz", 12)
  val () = if (err < 0) then let
    val () = perror "sethostname" in (*none*)
  end // end of [val]
//
  var !p_buf with pf_buf = @[byte][128]()
  val (pfopt | err) = getdomainname (pf_buf | p_buf, 128)
  val () = assertloc (err >= 0)
  prval getdomainname_v_succ pf = pfopt
  val () = (print "getdomainname() = "; print_strbuf (!p_buf); print_newline ())
  prval () = pf_buf := bytes_v_of_strbuf_v (pf)
//
  val err = setdomainname ("xxx.yyy.zzz", 12)
  val () = if (err < 0) then let
    val () = perror "setdomainname" in (*none*)
  end // end of [val]
//
} // end of [main]

(* ****** ****** *)

(* end of [libc_unistd.dats] *)
