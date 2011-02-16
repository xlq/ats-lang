(*
**
*)

(* ****** ****** *)
//
// Author: Hongwei Xi (* hwxi AT cs DOT bu DOT edu *)
// 14 February 2011:
//
(* ****** ****** *)

staload "libc/SATS/dirent.sats"

(*
fun dirent_stream_vt_make_DIR {l_dir:addr}
  (pf: DIR @ l_dir | p: ptr l_dir):<!laz> stream_vt (dirent)
// end of [dirent_strean_vt_make_DIR]
*)

(* ****** ****** *)

extern
fun{a:t@ype}
doit {l:agz} (dirname: string, name: !strptr l): void

fun{a:t@ype}
myfind (dirname: string): void = let
  val (pf_dir | p_dir) = opendir_exn (dirname)
  val xs = dirent_stream_vt_make_DIR (pf_dir | p_dir)
  fun loop (
    xs: stream_vt (dirent)
  ) :<cloref1> void = let
    val xs_con = !xs
  in
    case+ xs_con of
    | stream_vt_cons (!p_x, xs) => let
        val (fpf_name | name) = dirent_get_d_name (!p_x)
        val () = doit<a> (dirname, name)
        prval () = fpf_name (name)
        val () = free@ {dirent} (xs_con)
      in
        loop (xs)
      end // end of [stream_vt_cons]
    | ~stream_vt_nil () => ()
  end // endof [loop]
  val () = loop (xs)
in
  // nothing
end // end of [myfind]

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

implement
doit<void> (dirname, name) = let
  val () = case+ $UN.castvwtp1 {string} (name) of
    | "." => ()
    | ".." => ()
    | name when test_file_isdir (name) => let
        val dirname = sprintf ("%s/%s", @(dirname, name))
        val () = myfind<void> ($UN.castvwtp1 {string} (dirname))
        val () = strptr_free (dirname)
      in
        // nothing
      end // end of [_ when ...]
    | name => println! (dirname, "/", name)
  // end of [val]
in
  // nothing
end // end of [doit<void>]

(* ****** ****** *)

implement main () = myfind<void> (".")

(* ****** ****** *)

(* end of [myfind.dats] *)
