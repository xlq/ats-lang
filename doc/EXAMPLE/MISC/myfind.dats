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
fun doit {l:agz}
  (dirname: string, name: !strptr l): void
// end of [doit]

fun myfind (dirname: string): void = let
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
        val () = doit (dirname, name)
        prval () = fpf_name (name)
        val () = free@ {dirent} (xs_con)
      in
        loop (xs)
      end // end of [stream_vt_cons]
    | ~stream_vt_nil () => ()
  end // end of [loop]
  val () = loop (xs)
in
  // nothing
end // end of [myfind]

(* ****** ****** *)

staload S = "libc/sys/SATS/stat.sats"
staload T = "libc/sys/SATS/types.sats"
staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

fun isexec (x: int) = let
  val m = $T.uint_of_mode ($S.S_IXUSR) land (uint_of_int (x))
in
  if m > 0U then true else false
end // end of [isexec]

(* ****** ****** *)

implement
doit (dirname, name) = let
  val () = case+ $UN.castvwtp1 {string} (name) of
    | "." => ()
    | ".." => ()
    | name when test_file_isdir (name) => let
        val dirname = sprintf ("%s/%s", @(dirname, name))
        val () = myfind ($UN.castvwtp1 {string} (dirname))
        val () = strptr_free (dirname)
      in
        // nothing
      end // end of [_ when ...]
    | name => println! (dirname, "/", name)
  // end of [val]
in
  // nothing
end // end of [doit]

(*
implement
doit (dirname, name) = let
  val () = case+ $UN.castvwtp1 {string} (name) of
    | "." => ()
    | ".." => ()
    | name when test_file_isdir (name) => let
        val () = $S.chmod_exn (name, $T.mode_of_int (0755))
        val dirname = sprintf ("%s/%s", @(dirname, name))
        val () = myfind ($UN.castvwtp1 {string} (dirname))
        val () = strptr_free (dirname)
      in
        // nothing
      end // end of [_ when ...]
    | name when test_file_islnk (name) => ()
    | name when test_file_isreg (name) => let
        val m = (
          if test_file_mode (name, isexec) then 0755 else 0644
        ) : int // end of [val]
      in
        $S.chmod_exn (name, $T.mode_of_int (m))
      end // end of [_ when ...]
    | _ => () // end of [_]
  // end of [val]
in
  // nothing
end // end of [doit]
*)

(* ****** ****** *)

implement main () = myfind (".")

(* ****** ****** *)

(* end of [myfind.dats] *)
