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

%{^
static
int hello_readdir (
  const char *path
, void *buf
, fuse_fill_dir_t filler
, off_t offset
, struct fuse_file_info *fi
) {
    (void) offset; (void) fi;
//
    if (strcmp(path, "/") != 0) return -ENOENT;
//
    filler (buf, ".", NULL, 0) ;
    filler (buf, "..", NULL, 0) ;
    filler (buf, hello_path + 1, NULL, 0) ;
//
    return 0;
} // end of [hello_readdir]
%} // end of [%{^]
extern
fun hello_readdir (
  path: string, buf: ptr, filler: fuse_fill_dir_t, offset: off_t
) : int // 0/1: succ/fail

(* ****** ****** *)

%{^
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
%} // end of [%{^]
extern
fun hello_open
  (path: string, fi: &fuse_file_info): int = "#hello_open"
// end of [hello_open]

(* ****** ****** *)

(*
%{^
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
%} // end of [%{^]
*)
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
) : ssize_t = "hello_read"
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
    ssize_of_size(hello_read_main (pf | path, p_buf, n, ofs, fi))
  else ssize_of_int(~int_of_errno(res))
end // end of [hello_read]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$

static
struct fuse_operations
hello_oper = {
  .getattr= hello_getattr,
  .readdir= hello_readdir,
  .open= hello_open,
  .read= hello_read,
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
