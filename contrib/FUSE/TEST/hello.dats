/*
    FUSE: Filesystem in Userspace
    Copyright (C) 2001-2005  Miklos Szeredi <miklos@szeredi.hu>

    This program can be distributed under the terms of the GNU GPL.
    See the file COPYING.
*/

//
// Translated from C into ATS by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)

staload "dummy.sats"
staload "libc/SATS/errno.sats"
staload "libc/SATS/fcntl.sats"
staload "libc/SATS/stdio.sats"
staload "libc/SATS/string.sats"
staload "libc/sys/SATS/stat.sats"

staload "contrib/FUSE/SATS/fuse.sats"

(* ****** ****** *)

%{^
static char *hello_str = "Hello World!\n" ;
static char *hello_path = "/hello" ;
%} // end of [%{^]

(* ****** ****** *)

%{^
static
int hello_getattr(
  const char *path, struct stat *stbuf
) {
    int res = 0;
//
    memset(stbuf, 0, sizeof(struct stat));
//
    if(strcmp(path, "/") == 0) {
        stbuf->st_mode = S_IFDIR | 0755;
        stbuf->st_nlink = 2;
    }
    else if(strcmp(path, hello_path) == 0) {
        stbuf->st_mode = S_IFREG | 0444;
        stbuf->st_nlink = 1;
        stbuf->st_size = strlen(hello_str);
    }
    else
        res = -ENOENT;
    // end of [if]
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
    filler(buf, ".", NULL, 0);
    filler(buf, "..", NULL, 0);
    filler(buf, hello_path + 1, NULL, 0);
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
    if(strcmp(path, hello_path) != 0) return -ENOENT;
    if((fi->flags & 3) != O_RDONLY) return -EACCES;
    return 0;
} // end of [hello_open]
%} // end of [%{^]
extern
fun hello_open (path: string, fi: &fuse_file_info): int = "#hello_open"

(* ****** ****** *)

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
    if(strcmp(path, hello_path) != 0) return -ENOENT;
//
    len = strlen(hello_str);
    if (offset < len) {
        if (offset + size > len) size = len - offset;
        memcpy(buf, hello_str + offset, size);
    } else
        size = 0;
    // end of [if]
//
    return size;
} // end of [hello_read]
%} // end of [%{^]
extern
fun hello_read (
  path: string, buf: ptr, size: size_t, offset: off_t, fi: &fuse_file_info
) : int = "#hello_read"

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
