//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)
//
// book: AUP (2nd edition), pages 204 - 224
// section: 4.2: Reading from a Terminal
//
(* ****** ****** *)

staload "libc/SATS/fcntl.sats"
staload "libc/SATS/unistd.sats"

(* ****** ****** *)

#include "prelude/HATS/lmacrodef.hats"

(* ****** ****** *)

fun getln {n:pos} (
    s: &bytes(n), nmax: size_t n, iseof: &bool >> bool
  ) : bool = let
  val (pf_fd | ()) = stdin_fildes_view_get ()
  prval pf_lte = open_flag_lte_rd_rd
  val nread = fildes_read_err (pf_lte, pf_fd | STDIN_FILENO, s, nmax - 1)
//
  val res = (case+ 0 of
| _ when nread > 0 => true where {
    val () = iseof := false
    val nread = size1_of_ssize1 (nread)
    val nread1 = nread - 1
    macdef NUL = byte_of_char('\0')
    val () = if s.[nread1] = (byte_of_char)'\n'
      then s.[nread1] := NUL else s.[nread] := NUL
    // end of [val]
  } // end of [_ when ...]
| _ when nread >= 0 => true where {
    val () = iseof := true
  } // end of [_ when ...]
| _ (* nread=-1 *) => false
  ) : bool // end of [val]
//
  val () = stdin_fildes_view_set (pf_fd | (*none*))
in
  res
end // end of [getln]

(* ****** ****** *)

#define BUFSZ 1024

implement
main () = () where {
  var !p_buf with pf_buf = @[byte][BUFSZ]()
  prval () = pf_buf := bytes_v_of_b0ytes_v (pf_buf)
  var iseof: bool = false
  val () = println "Please input:"
  val () = while (true) let
    val err = getln (!p_buf, BUFSZ, iseof)
    val () = if ~err then break
    val () = if iseof then
      printf ("EOF\n", @())
    else
      printf ("Read: %s\n", @(__cast p_buf)) where {
        extern castfn __cast (x: ptr): string // cutting a corner
      } // end of [where]
    // end of [val]
    val () = if iseof then break
  in
    // nothing
  end // end of [val]
} // end of [main]

(* ****** ****** *)

(* end of [AUP_4_2.dats] *)
