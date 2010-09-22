//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//

(* ****** ****** *)
//
// book: AUP (2nd edition), pages 147 - 158
// section: 3.5: Accessing and Displaying File Metadata
//
(* ****** ****** *)

staload "libc/SATS/errno.sats"
staload "libc/SATS/grp.sats"
staload "libc/SATS/pwd.sats"
staload "libc/SATS/unistd.sats"
staload "libc/sys/SATS/stat.sats"
staload "libc/sys/SATS/types.sats"

(* ****** ****** *)

fun print_mode .<>.
  (st: &stat_t): void = let
  val mode = st.st_mode
//
  macdef TYPE(b) = ,(b) = (mode land S_IFMT)
  macdef MODE(b) = ,(b) = (mode land ,(b))
//
  val () = case+ 0 of
    | _ when TYPE(S_IFBLK) => print 'b'
    | _ when TYPE(S_IFCHR) => print 'c'
    | _ when TYPE(S_IFDIR) => print 'd'
    | _ when TYPE(S_IFIFO) => print 'p'
    | _ when TYPE(S_IFLNK) => print 'l'
    | _ when TYPE(S_IFREG) => print '-'
    | _ when TYPE(S_IFSOCK) => print 's'
    | _ => print '?'
  // end of [val]
//
  val () = if MODE(S_IRUSR) then print 'r' else print '-'
  val () = if MODE(S_IWUSR) then print 'w' else print '-'
  val () = case+ 0 of
    | _ when MODE(S_ISUID) =>
       if MODE(S_IXUSR) then print 's' else print 'S'
    | _ => 
       if MODE(S_IXUSR) then print 'x' else print '-'
   // end of [val]
//
  val () = if MODE(S_IRGRP) then print 'r' else print '-'
  val () = if MODE(S_IWGRP) then print 'w' else print '-'
  val () = case+ 0 of
    | _ when MODE(S_ISGID) =>
       if MODE(S_IXGRP) then print 's' else print 'S'
    | _ => 
       if MODE(S_IXGRP) then print 'x' else print '-'
   // end of [val]
//
  val () = if MODE(S_IROTH) then print 'r' else print '-'
  val () = if MODE(S_IWOTH) then print 'w' else print '-'
  val () = case+ 0 of
    | _ when MODE(S_IFDIR) andalso MODE(S_ISVTX) =>
       if MODE(S_IXOTH) then print 't' else print 'T'
    | _ => 
       if MODE(S_IXOTH) then print 'x' else print '-'
   // end of [val]
//
in
  // nothing
end // end of [print_mode]

(* ****** ****** *)

fun print_nlink .<>.
  (st: &stat_t): void = let
  val nlink = st.st_nlink
  val nlink = lint_of_nlink (nlink)
in
  printf ("%5ld", @(nlink))
end // end of [print_nlink]

(* ****** ****** *)

fun print_owner .<>.
  (st: &stat_t): void = let
  val uid = st.st_uid
  val (pfopt| p) = getpwuid (uid)
in
  if p > null then let
    prval Some_v @(pf, fpf) = pfopt
    val (fpf_x | x) = passwd_get_pw_name (!p)
    prval () = fpf (pf)
    val () = assert_errmsg (strptr_isnot_null x, #LOCATION)
    val () = printf (" %-8s", @(__cast x)) where {
      extern castfn __cast {l:addr} (x: !strptr l):<> string
    }
    prval () = fpf_x (x)
  in
    // nothing
  end else let
    prval None_v () = pfopt
    val uid = lint_of_uid (uid)
  in
    printf (" %-8ld", @(uid))
  end // end of [if]
end (* end of [print_owner] *)

(* ****** ****** *)

fun print_group .<>.
  (st: &stat_t): void = let
  val gid = st.st_gid
  val (pfopt| p) = getgrgid (gid)
in
  if p > null then let
    prval Some_v @(pf, fpf) = pfopt
    val (fpf_x | x) = group_get_gr_name (!p)
    prval () = fpf (pf)
    val () = assert_errmsg (strptr_isnot_null x, #LOCATION)
    val () = printf (" %-8s", @(__cast x)) where {
      extern castfn __cast {l:addr} (x: !strptr l):<> string
    }
    prval () = fpf_x (x)
  in
    // nothing
  end else let
    prval None_v () = pfopt
    val gid = lint_of_gid (gid)
  in
    printf (" %-8ld", @(gid))
  end // end of [if]
end (* end of [print_group] *)

(* ****** ****** *)

implement
main (argc, argv) = () where {
  val path = (if argc >= 2 then argv.[1] else "."): string
//
  var stat: stat_t? // uinitialized
  val () = lstat_exn (path, stat) 
  val () = print_mode (stat)
  val () = print_nlink (stat)
  val () = print_owner (stat)
  val () = print_group (stat)
  val () = print_newline ()
//
} // end of [main]

(* ****** ****** *)

(* end of [AUP_3_5.dats] *)
