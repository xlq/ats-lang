/*
    FUSE: Filesystem in Userspace
    Copyright (C) 2001-2005  Miklos Szeredi <miklos@szeredi.hu>

    This program can be distributed under the terms of the GNU GPL.
    See the file COPYING.
*/

(* ****** ****** *)

//
// Modified from C into ATS by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%} // end of [%{^]

(* ****** ****** *)

staload "myheader.sats"
staload "libc/SATS/errno.sats"
staload "libc/SATS/fcntl.sats"
staload "libc/SATS/stdio.sats"
staload "libc/SATS/string.sats"
staload "libc/sys/SATS/stat.sats"
staload "libc/sys/SATS/types.sats"

staload "contrib/FUSE/SATS/fuse.sats"

(* ****** ****** *)

%{^
static char *hello_str = "Hello, world!\n" ;
static char *hello_path = "/hello" ;
%} // end of [%{^]
extern val hello_str : string = "#hello_str"
extern val hello_path : string = "#hello_path"

(* ****** ****** *)

(*
#define LOGFILENAME "/tmp/hello_log"
extern fun log_int (msg: int): void = "log_int"
implement log_int (msg) = let
  val fil = fopen_ref_exn (LOGFILENAME, file_mode_aa)
  val () = fprint_int (fil, msg)
  val () = fprint_newline (fil)
  val () = fclose_exn (fil)
in
  // nothing
end // end of [log_int]
extern fun log_string (msg: string): void = "log_string"
implement log_string (msg) = let
  val fil = fopen_ref_exn (LOGFILENAME, file_mode_aa)
  val () = fprint_string (fil, msg)
  val () = fclose_exn (fil)
in
  // nothing
end // end of [log_string]
*)

(* ****** ****** *)

%{^
static
int hello_getattr (
  const char *path, struct stat *stbuf
) {
    int res = 0;
//
    memset (stbuf, 0, sizeof(struct stat));
//
    if (strcmp(path, "/") == 0) {
      stbuf->st_mode = (S_IFDIR | 0755) ;
      stbuf->st_nlink = 2 ;
    } else if (strcmp(path, hello_path) == 0) {
      stbuf->st_mode = (S_IFREG | 0444) ;
      stbuf->st_nlink = 1 ;
      stbuf->st_size = strlen (hello_str) ;
    } else {
      res = -ENOENT;
    } // end of [if]
//
    return res;
} // end of [hello_getattr]
%} // end of [%{^]
extern
fun hello_getattr (
  path: string, buf: &stat? >> opt (stat, i==0)
) : #[i:int | i <= 0] int i = "#hello_getattr"

(* ****** ****** *)

/*
%{^
static
int hello_readdir (
  const char *path
, void *buf
, fuse_fill_dir_t filler
, off_t offset
, struct fuse_file_info *fi
) {
  (void)offset; (void)fi;
  if (strcmp(path, "/") != 0) return -ENOENT;
  filler (buf, ".", NULL, 0) ;
  filler (buf, "..", NULL, 0) ;
  filler (buf, hello_path + 1, NULL, 0) ;
  return 0;
} // end of [hello_readdir]
%}
*/
extern
fun hello_readdir (
  path: string
, buf: ptr, filler: fuse_fill_dir_t, ofs: off_t
, fi: &fuse_file_info
) : int = "hello_readdir" // 0/1: succ/fail
// (*
implement
hello_readdir (
  path, buf, filler, ofs, fi
) = let
(*
  val () = log_string "hello_readdir(bef)\n"
*)
  var res: int = 0
  val () = while (true) let
    val test = (path = "/")
    val () = if ~test then
      (res := ~int_of(ENOENT); break)
    val filler = __cast (filler) where {
      // HX: [off_t] cannot be changed to [int]!!!
      extern castfn __cast (x: fuse_fill_dir_t): (ptr, string, ptr, off_t) -> int
    } // end of [val]
    val _0 = (off_of_lint)0L
    val _err = filler (buf, ".", null, _0)
    val _err = filler (buf, "..", null, _0)
    val hpath1 = __tail (hello_path) where {
      extern fun __tail (x: string):<> string = "atspre_psucc"
    } // end of [val]
    val _err = filler (buf, hpath1, null, _0)
  in
    break
  end // end of [val]
(*
  val () = log_string "hello_readdir(aft)\n"
*)
in
  res (* 0/neg : succ/fail *)
end // end of [hello_readdir]
// *)

(* ****** ****** *)

/*
static
int hello_open (
  const char *path
, struct fuse_file_info *fi
) {
//
    if (strcmp(path, hello_path)) return -ENOENT ;
//
    if ((fi->flags & 3) != O_RDONLY) return -EACCES ;
//
    return 0;
//
} // end of [hello_open]
*/
extern
fun hello_open
  (path: string, fi: &fuse_file_info): int = "hello_open"
// end of [hello_open]
implement
hello_open (path, fi) = let
  var res: int = 0
  val () = while (true) let
    val test =  path = hello_path
    val () = if ~test then (res := ~(int_of)ENOENT; break)
    val test = ((fi.flags land 0x3U) = (uint_of)O_RDONLY)
    val () = if ~test then (res := ~(int_of)EACCES; break)
  in
    break
  end // end of [val]
in
  res (* 0/neg : succ/fail *)
end // end of [hello_open]

(* ****** ****** *)

/*
static
int hello_read (
  const char *path
, char *buf
, size_t size
, off_t offset
, struct fuse_file_info *fi
) {
    size_t len; (void) fi;
//
    if (strcmp(path, hello_path) != 0) return -ENOENT;
//
    len = strlen (hello_str);
//
    if (offset < len) {
      if (offset + size > len) size = len - offset;
      memcpy (buf, hello_str + offset, size);
    } else
      size = 0;
    // end of [if]
//
    return size;
} // end of [hello_read]
*/
//
// HX-2010-09-30:
// this is really an overkill, but the idea is demonstrated ...
//
extern
fun hello_read_main {n1,n2:nat} {l:addr} (
    pf: !bytes n1 @ l
  | path: string, p_buf: ptr l, n1: size_t n1, ofs: size_t n2, fi: &fuse_file_info
) : sizeLte (n1) = "hello_read_main"
implement
hello_read_main {n1,n2}
  (pf | path, p_buf, n1, ofs, fi) = let
  val [len:int] str = (string1_of_string)hello_str
  val len = string1_length (str)
in
//
if ofs <= len then let
  stavar len1: int
  val len1: size_t (len1) = min (n1, len-ofs)
  val (fpf_ofs, pf_ofs | p_ofs) = __takeout (str, ofs) where {
     extern fun __takeout {n2 + len1 <= len} (x: string len, ofs: size_t n2)
       :<> [l_ofs:addr] (bytes len1 @ l_ofs -<lin,prf> void, bytes len1 @ l_ofs | ptr l_ofs)
       = "#atspre_padd_size"
     // end of [__takeout]
  } // end of [val]
  val _err = memcpy (pf | p_buf, !p_ofs, len1)
  var i: natLte len1
  #define b2c char_of_byte
  #define c2b byte_of_char
  val () = for (i := 0; i < len1; i := i+1) let
    val c = b2c(p_buf->[i]) in p_buf->[i] := c2b (char_toupper(c)) // turning into uppercase
  end // end of [val]
  prval () = fpf_ofs (pf_ofs)
in
  len1
end else (size1_of_int1)0
//
end // end of [hello_read_main]
extern
fun hello_read {n:nat} {l:addr} (
    pf: !bytes n @ l
  | path: string, p_buf: ptr l, n: size_t n, ofs: off_t, fi: &fuse_file_info
) : int = "hello_read"
implement hello_read
  (pf | path, p_buf, n, ofs, fi) = let
  var res: errno_t = ENONE
  val () = if res = ENONE then (
    if (path <> hello_path) then res := ENOENT
  ) // end of [if]
  val ofs = lint_of_off (ofs)
  val () = if res = ENONE then (if ofs < 0L then res := EINVAL)
  val ofs = ulint_of_lint (ofs)
  val ofs = size_of_ulint (ofs)
  val ofs = size1_of_size (ofs)
in
  if res = ENONE then
    int_of_size(hello_read_main (pf | path, p_buf, n, ofs, fi))
  else ~int_of_errno(res)
end // end of [hello_read]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$

static
struct fuse_operations
hello_oper = {
  .getattr= hello_getattr,
  .readdir= (fuse_readdir_t)hello_readdir,
  .open= (fuse_open_t)hello_open,
  .read= (fuse_read_t)hello_read,
} ; // end of [fuse_operations]

ats_void_type
mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  fuse_main (argc, (char**)argv, &hello_oper, NULL) ;
  return ;
} // end of [mainats]
%} // end of [%{$]

(* ****** ****** *)

(* end of [hello.dats] *)
