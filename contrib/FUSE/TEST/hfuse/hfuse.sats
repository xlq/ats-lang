/*
** HFUSE: FUSE file system (modular) for AWS S3
** Mark Reynolds
*/

(* ****** ****** *)

(*
** HX: adapting Mark's C code to ATS
*)

(* ****** ****** *)

staload "contrib/FUSE/SATS/fuse.sats"

(* ****** ****** *)

absview hfuselog_v
fun hfuselog_lock ():<> (hfuselog_v | void)
fun hfuselog_unlock (pf: hfuselog_v | (*none*)):<> void

(* ****** ****** *)

fun tfprintf {ts:types}
  (pf: !hfuselog_v | fmt: printf_c (ts), arg: ts): int = "tfprintf"
// end of [tfprintf]

(* ****** ****** *)

fun dologtime(pf: !hfuselog_v | (*none*)): void  = "dologtime"

(* ****** ****** *)

fun parts {n:pos} (
  path: string n, n: size_t n
, bname: &strptr? >> strptr0, rname: &strptr? >> strptr0
) : void = "parts"

(* ****** ****** *)

fun hfuse_open (path: string, fi: &fuse_file_info): int = "hfuse_open"

(* ****** ****** *)

fun hfuse_read
  {n:nat} {l:addr} (
    pf: !bytes n @ l
  | path: string, p_buf: ptr l, n: size_t n, ofs: off_t, fi: &fuse_file_info
) : ssize_t = "hfuse_read"

(* ****** ****** *)

fun hfuse_release (path: string, fi: &fuse_file_info): int = "hfuse_release"

(* ****** ****** *)

(* end of [hfuse.sats] *)
