//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Summer, 2009
//

(* ****** ****** *)
//
// book: AUP (2nd edition), pages 170 - 174
// section 3.6.4: Implementing getcwd (walking up the tree)
//
(* ****** ****** *)

staload "libc/sys/SATS/stat.sats"
staload "libc/sys/SATS/types.sats"

(* ****** ****** *)

staload "libc/SATS/errno.sats"
staload "libc/SATS/fcntl.sats"
staload "libc/SATS/dirent.sats"
staload "libc/SATS/stdlib.sats"
staload "libc/SATS/unistd.sats"

(* ****** ****** *)

viewtypedef pathlist = List_vt (strptr0)

(* ****** ****** *)

fun push_pathlist
  (lstrs: &pathlist, name: string): void = let
  val name = string1_of_string name
  val n = string1_length (name)
  val (pf_gc, pf_buf | p) = string_make_substring (name, 0, n)
  val lstr = strptr_of_strbuf @(pf_gc, pf_buf | p)
in
  lstrs := list_vt_cons {strptr0} (lstr, lstrs)
end (* end of [push_pathlist] *)

fun free_pathlist (ps: pathlist): void = case+ ps of
  | ~list_vt_cons (p, ps) => (strptr_free p; free_pathlist ps)
  | ~list_vt_nil () => ()
// end of [free_pathlist]

(* ****** ****** *)

extern fun getcwdx (): strptr0

(* ****** ****** *)

fn SAME_INODE (s1: &stat_t, s2: &stat_t): bool =
  (stat_st_dev_get s1 = stat_st_dev_get s2) andalso
  (stat_st_ino_get s1 = stat_st_ino_get s2)
// end of [SAME_INODE]

(* ****** ****** *)

macdef errno_is_ENOENT () = (errno_get () = ENOENT)

fun loop_dir (
    ents: stream_vt dirent_t, stat: &stat_t, lstrs: &pathlist, nent: int
  ) : int = case+ !ents of
  | ~stream_vt_cons (ent, ents) => let
      var ent = ent
      val d_name = dirent_d_name_get (ent)
      var stat_entry: stat_t? // uninitialized
      val rtn = lstat_err (d_name, stat_entry)
    in
      if rtn >= 0 then let
        prval () = opt_unsome (stat_entry)
      in
        case+ 0 of
        | _ when SAME_INODE (stat, stat_entry) => let
            val () = ~ents
            val () = if nent > 0 then push_pathlist (lstrs, "/")
            val () = push_pathlist (lstrs, d_name)
          in  
            1 // the entry for the current directory is found
          end // end of [_ when ...]  
        | _ => loop_dir (ents, stat, lstrs, nent)
      end else let
        prval () = opt_unnone (stat_entry)
        val () = ~ents
      in
        0 (* error *)
      end // end of [if]
    end (* end of [stream_vt_cons] *)
   | ~stream_vt_nil () => 0 (* error *)
// end of [loop_dir]

fun getcwdx_main {fd:int} (
    pf_fd: fildes_v (fd, open_flag_rd) | fd: int fd, stat: &stat_t
  ) : strptr0 = let
  var err: int = 0
  var lstrs: pathlist = list_vt_nil ()
  val () = loop (pf_fd | fd, stat, lstrs, 0(*nent*), err) where {
    fun loop {fd:int} {flag:open_flag} (
        pf_fd: !fildes_v (fd, flag)
      | fd: int fd, stat: &stat_t, lstrs: &pathlist, nent: int, err: &int
      ) : void = let
      var stat_parent: stat_t? // uninitialized
      val rtn = lstat_err ("..", stat_parent)
    in
      if rtn >= 0 then let
        prval () = opt_unsome (stat_parent)
        val rtn = chdir_err ".."
        val term = if :(stat_parent: stat_t) => 
          (rtn = ~1  andalso errno_is_ENOENT ()) then true else SAME_INODE (stat, stat_parent)
        // end of [val]
      in
        case+ 0 of
        | _ when term => push_pathlist (lstrs, "/") // for leading "/"
        | _ when rtn = ~1 => (err := err + 1) // loop exists abnormally
        | _ (*continue*) => let
            val (pfopt_dir | p_dir) = opendir_err (".")
          in
            if p_dir <> null then let
              prval Some_v pf_dir = pfopt_dir
              val ents = dirent_stream_vt_make_DIR (pf_dir | p_dir)
              val found = loop_dir (ents, stat, lstrs, nent)
            in
              if found > 0 then let
                val () = stat := stat_parent in loop (pf_fd | fd, stat, lstrs, nent+1, err)
              end else begin
                errno_set (ENOENT); err := err + 1
              end // end of [if]
            end else let
              prval None_v () = pfopt_dir in err := err + 1 // loop exits abnormally 
            end (* end of if *)
          end (* end of [_(*continue*)] *)
      end else let
        prval () = opt_unnone (stat_parent)
      in
        err := err + 1 // loop exits abnormally
      end // end of [if]  
    end (* end of [loop] *)
  } // end of [val]
  val () = fchdir_exn (pf_fd | fd)
  val () = close_exn (pf_fd | fd)
  val () = if (err > 0) then (free_pathlist lstrs; lstrs := list_vt_nil)
  val lstrs = lstrs
in
  case+ lstrs of
  | list_vt_cons _ => let
      val () = fold@ lstrs
      val path =
        stringlst_concat (__cast lstrs) where {
        extern castfn __cast (lstrs: !pathlist): List string
      } // end of [val]
      val () = free_pathlist (lstrs)
    in
      path
    end // end of [list_vt_cons]
  | ~list_vt_nil () => strptr_null (null)
end // end of [getcwdx_main]

(* ****** ****** *)

implement getcwdx () = let
  var stat: stat_t? // uinitialized
  val (pfopt_fd | fd) = open_flag_err (".", O_RDONLY)
in
  if fd <> ~1 then let
    prval open_v_succ pf_fd = pfopt_fd
    val rtn = lstat_err (".", stat) 
  in
    if rtn >= 0 then let
      prval () = opt_unsome (stat)
    in
      getcwdx_main (pf_fd | fd, stat)
    end else let
      prval () = opt_unnone (stat)
    in
      close_exn (pf_fd | fd); strptr_null (null)
    end // end of [if]
  end else let
    prval open_v_fail () = pfopt_fd in strptr_null (null)
  end // end of [if]  
end (* end of [getcwdx] *)

(* ****** ****** *)

implement main () = let
  val [l:addr] path = getcwdx ()
  prval () = addr_is_gtez {l} ()
in
  if strptr_isnot_null path then let
    val () =
      printf ("%s\n", @(__cast path)) where {
      extern castfn __cast {l:agz} (x: !strptr l): string
    }
    val () = strptr_free (path)
  in
    exit (EXIT_SUCCESS)
  end else let
    val _null = strptr_free_null (path) in exit (EXIT_FAILURE)
  end // end of [if] 
end (* end of [main] *)

(* ****** ****** *)

(* end of [AUP_3_6_4.dats] *)
