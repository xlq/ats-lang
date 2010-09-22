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
  val st_mode = stat_get_st_mode (st)
//
  macdef TYPE(b) = ,(b) = (st_mode land S_IFMT)
  macdef MODE(b) = ,(b) = (st_mode land ,(b))
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
  val n = stat_get_st_nlink (st)
  val n = lint_of_nlink (n)
in
  printf ("%5ld", @(n))
end // end of [print_nlink]

(* ****** ****** *)

%{^
#define passwd_get_pw_name(x) (((ats_passwd_type*)x)->pw_name)
%}
extern
fun passwd_get_pw_name (pwd: &passwd_t): string = "#passwd_get_pw_name"

fun print_owner .<>.
  (st: &stat_t): void = let
  val uid = stat_get_st_uid (st)
  val (pfopt| p) = getpwuid (uid)
in
  if p > null then let
    prval Some_v @(pf, fpf) = pfopt
    val name = passwd_get_pw_name (!p)
    prval () = fpf (pf)
  in
    printf (" %-8s", @(name))
  end else let
    prval None_v () = pfopt
    val uid = lint_of_uid (uid)
  in
    printf (" %-8ld", @(uid))
  end // end of [if]
end (* end of [print_owner] *)

(* ****** ****** *)

%{^
#define group_get_gr_name(x) (((ats_group_type*)x)->gr_name)
%}
extern
fun group_get_gr_name (grp: &group_t): string = "#group_get_gr_name"

fun print_group .<>.
  (st: &stat_t): void = let
  val gid = stat_get_st_gid (st)
  val (pfopt| p) = getgrgid (gid)
in
  if p > null then let
    prval Some_v @(pf, fpf) = pfopt
    val name = group_get_gr_name (!p)
    prval () = fpf (pf)
  in
    printf (" %-8s", @(name))
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
