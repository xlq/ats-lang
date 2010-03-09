//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: Summer, 2009
//

(* ****** ****** *)

// book: AUP (2nd edition), pages 170 - 174

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

absviewtype lstring

extern castfn lstring_make {m,n:nat} {l:addr}
  (pf_gc: free_gc_v (m, l), pf_buf: strbuf (m, n) @ l | p: ptr l) :<> lstring
// end of [lstring_make]

%{^

ats_void_type
lstring_free (ats_ptr_type s) { ATS_FREE(s); return ; }
// end of [lstring_free]

%}

extern fun lstring_free (s: lstring): void = "lstring_free"

(* ****** ****** *)

absviewtype lstringopt (bool)

%{^

ats_ptr_type lstringopt_none () { return (ats_ptr_type)0 ; }

ats_void_type lstringopt_unnone (ats_ptr_type lstropt) { return ; }

ats_bool_type 
lstringopt_is_some (ats_ptr_type lstropt) {
  return (lstropt ? ats_true_bool : ats_false_bool) ;
}

%}

extern fun lstringopt_none (): lstringopt (false)
  = "lstringopt_none"

extern fun lstringopt_unnone (lstropt: lstringopt (false)): void
  = "lstringopt_unnone"

extern castfn lstringopt_some (lstr: lstring): lstringopt (true)
extern castfn lstringopt_unsome (lstropt: lstringopt (true)): lstring

extern fun lstringopt_is_some {b:bool} (lstropt: !lstringopt b): bool (b)
  = "lstringopt_is_some"
  
(* ****** ****** *)

viewtypedef pathlist = List_vt (lstring)

(* ****** ****** *)

fun push_pathlist
  (lstrs: &pathlist, name: string): void = let
  val name = string1_of_string name
  val n = string1_length (name)
  val (pf_gc, pf_buf | p) = string_make_substring (name, 0, n)
  val lstr = lstring_make (pf_gc, pf_buf | p)
in
  lstrs := list_vt_cons {lstring} (lstr, lstrs)
end (* end of [push_pathlist] *)

fun free_pathlist (ps: pathlist): void = case+ ps of
  | ~list_vt_cons (p, ps) => (lstring_free p; free_pathlist ps)
  | ~list_vt_nil () => ()
// end of [free_pathlist]

(* ****** ****** *)

extern fun getcwdx (): [b:bool] lstringopt (b)

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
      val (pfopt | rtn) = lstat_err (view@ stat_entry | d_name, &stat_entry)
    in
      if rtn <> ~1 then let
        prval stat_v_succ pf = pfopt; prval () = view@ stat_entry := pf 
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
        prval stat_v_fail pf = pfopt
        prval () = view@ stat_entry := pf 
        val () = ~ents
      in
        0 (* error *)
      end // end of [if]
    end (* end of [stream_vt_cons] *)
   | ~stream_vt_nil () => 0 (* error *)
// end of [loop_dir]

fun getcwdx_main {fd:int} (
    pf_fd: fildes_v (fd, open_flag_rd) | fd: int fd, stat: &stat_t
  ) : [b:bool] lstringopt (b) = let
  var err: int = 0
  var lstrs: pathlist = list_vt_nil ()
  val () = loop (pf_fd | fd, stat, lstrs, 0(*nent*), err) where {
    fun loop {fd:int} {flag:open_flag} (
        pf_fd: !fildes_v (fd, flag)
      | fd: int fd, stat: &stat_t, lstrs: &pathlist, nent: int, err: &int
      ) : void = let
      var stat_parent: stat_t? // uninitialized
      val (pfopt | rtn) = lstat_err (view@ stat_parent | "..", &stat_parent)
    in
      if rtn <> ~1 then let
        prval stat_v_succ pf = pfopt
        prval () = view@ stat_parent := pf
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
        prval stat_v_fail pf = pfopt
        prval () = view@ stat_parent := pf in
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
      val (pf_gc, pf_buf | p_path) =
      stringlst_concat (__cast lstrs) where {
        extern castfn __cast (lstrs: !pathlist): List string
      } // end of [val]
      val () = free_pathlist (lstrs)
      val path = lstring_make (pf_gc, pf_buf | p_path)
    in
      lstringopt_some (path)
    end // end of [list_vt_cons]
  | ~list_vt_nil () => lstringopt_none ()
end // end of [getcwdx_main]

(* ****** ****** *)

implement getcwdx () = let
  var stat: stat_t? // uinitialized
  val (pfopt_fd | fd) = open_flag_err (".", O_RDONLY)
in
  if fd <> ~1 then let
    prval open_v_succ pf_fd = pfopt_fd
    val (pfopt | rtn) = lstat_err (view@ stat | ".", &stat) 
  in
    if rtn <> ~1 then let
      prval stat_v_succ pf = pfopt; prval () = view@ stat := pf
    in
      getcwdx_main (pf_fd | fd, stat)
    end else let
      prval stat_v_fail pf = pfopt; prval () = view@ stat := pf
    in
      close_exn (pf_fd | fd); lstringopt_none ()
    end // end of [if]
  end else let
    prval open_v_fail () = pfopt_fd in lstringopt_none ()
  end // end of [if]  
end (* end of [getcwdx] *)

(* ****** ****** *)

implement main () = let
  val pathopt = getcwdx () in
  if lstringopt_is_some pathopt then let
    val path = lstringopt_unsome (pathopt)
    val () =
      printf ("%s\n", @(__cast path)) where {
      extern castfn __cast (lstr: !lstring): string 
    }
    val () = lstring_free (path)
  in
    exit (EXIT_SUCCESS)
  end else let
    val () = lstringopt_unnone (pathopt)
  in
    exit (EXIT_FAILURE)
  end // end of [if] 
end (* end of [main] *)

(* ****** ****** *)

(* end of [AUP_3_6_4.dats] *)
