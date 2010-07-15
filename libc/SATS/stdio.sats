(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
**
** Copyright (C) 2002-2008 Hongwei Xi, Boston University
**
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the  terms of the  GNU General Public License as published by the Free
** Software Foundation; either version 2.1, or (at your option) any later
** version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)
//
// This is essentially the first example of the its kind:
// building API for C functions
//
(* ****** ****** *)
//
// HX-07-13-2010:
// There are really two versions here: version-0 and version-1; the former
// is unsafe and prone to resource-leaks; it should be avoided once the programmer
// becomes comfortable with linear types in ATS.
//
(* ****** ****** *)

%{#
#include "libc/CATS/stdio.cats"
%} // end of [%{#]

(* ****** ****** *)

staload TYPES = "libc/sys/SATS/types.sats"
typedef whence_t = $TYPES.whence_t
macdef SEEK_SET = $TYPES.SEEK_SET
macdef SEEK_CUR = $TYPES.SEEK_CUR
macdef SEEK_END = $TYPES.SEEK_END

(* ****** ****** *)

sortdef fm = file_mode

//

typedef bytes (n:int) = @[byte][n]
typedef b0ytes (n:int) = @[byte?][n]

//

viewdef FILE_v (m:fm, l:addr) = FILE m @ l
viewdef FILE_opt_v (m:fm, l:addr) = option_v (FILE m @ l, l <> null)

//

praxi stdin_isnot_null : [stdin_addr > null] void
praxi stdout_isnot_null : [stdout_addr > null] void
praxi stderr_isnot_null : [stderr_addr > null] void

// ------------------------------------------------

macdef EOF = $extval (int, "EOF")

// ------------------------------------------------

(*

// void clearerr (FILE *stream);

The function [clearerr] clears the end-of-file and error indicators for
the stream pointed to by stream.

*)

fun clearerr0 (f: FILEref):<> void = "atslib_clearerr"
fun clearerr1 {m:fm} (f: &FILE m):<> void = "atslib_clearerr"

symintr clearerr
overload clearerr with clearerr0
overload clearerr with clearerr1

// ------------------------------------------------

(*

// int fclose (FILE *stream);

The [fclose] function will flush the stream pointed to by fp (writing any
buffered output data using [fflush] and close the underlying file
descriptor. The behaviour of [fclose] is undefined if the stream parameter
is an illegal pointer, or is a descriptor already passed to a previous
invocation of [fclose].

Upon successful completion 0 is returned.  Otherwise, EOF is returned and
the global variable errno is set to indicate the error.  In either case any
further access (including another call to fclose()) to the stream results
in undefined behaviour.

*)

fun fclose0_err
  (r: FILEref):<> int = "atslib_fclose_err"
// end of [fclose0_err]

fun fclose1_err
  {m:fm} {l:addr} (
    pf: !FILE_v (m, l) >> option_v (FILE_v (m, l), i == 0) | p: ptr l
  ) :<> #[i:int | i <= 0] int i
  = "atslib_fclose_err"
// end of [fclose1_err]

symintr fclose_err
overload fclose_err with fclose0_err
overload fclose_err with fclose1_err

//

fun fclose0_exn
  (r: FILEref):<!exn> void = "atslib_fclose_exn"
// end of [fclose0_exn]

fun fclose1_exn
  {m:fm} {l:addr} (pf: FILE m @ l | p: ptr l):<!exn> void
  = "atslib_fclose_exn"
// end of [fclose1_exn]

symintr fclose_exn
overload fclose_exn with fclose0_exn
overload fclose_exn with fclose1_exn

//

fun fclose_stdin ():<!exnref> void
  = "atslib_fclose_stdin"
fun fclose_stdout ():<!exnref> void
  = "atslib_fclose_stdout"
fun fclose_stderr ():<!exnref> void
  = "atslib_fclose_stderr"

// ------------------------------------------------

(*  

// int feof (FILE *stream);

The function feof() returns a nonzero value if the end of the given file
stream has been reached.

*)

fun feof0 (f: FILEref):<> int = "atslib_feof"
fun feof1 {m:fm} (f: &FILE m):<> int = "atslib_feof"

symintr feof
overload feof with feof0
overload feof with feof1

// ------------------------------------------------

(*

// int ferror (FILE *stream);

The function [ferror] tests the error indicator for the stream pointed to by
stream, returning non-zero if it is set.  The error indicator can only be
reset by the [clearerr] function.

*)

fun ferror0 (f: FILEref):<> int = "atslib_ferror"
fun ferror1 {m:fm} (f: &FILE m):<> int = "atslib_ferror"

symintr ferror
overload ferror with ferror0
overload ferror with ferror1

// ------------------------------------------------

(*

// int fflush (FILE *stream);

The function fflush forces a write of all user-space buffered data for the
given output or update stream via the streams underlying write function.
The open status of the stream is unaffected.

Upon successful completion 0 is returned.  Otherwise, EOF is returned and
the global variable errno is set to indicate the error.

*)

fun fflush0_err
  (f: FILEref):<> int = "atslib_fflush_err"
// end of [fflush0_err]

fun fflush1_err {m:fm}
  (pf: file_mode_lte (m, w) | f: &FILE m):<> [i:int | i <= 0] int i
  = "atslib_fflush_err"

symintr fflush_err
overload fflush_err with fflush0_err
overload fflush_err with fflush1_err

//

fun fflush0_exn (f: FILEref):<!exn> void
  = "atslib_fflush_exn"

fun fflush1_exn {m:fm}
  (pf: file_mode_lte (m, w) | f: &FILE m):<!exn> void
  = "atslib_fflush_exn"

symintr fflush_exn
overload fflush_exn with fflush0_exn
overload fflush_exn with fflush1_exn

fun fflush_stdout ():<!exnref> void = "atslib_fflush_stdout"

// ------------------------------------------------

(*

// int fgetc (FILE *stream)

[fgetc] reads the next character from stream and returns it as an
unsigned char cast to an int, or EOF on end of file or error.

*)

fun fgetc0_err (f: FILEref):<> int = "atslib_fgetc_err"

// [EOF] must be a negative number!
fun fgetc1_err
  {m:fm} (pf: file_mode_lte (m, r) | f: &FILE m):<> [i:int | i <= UCHAR_MAX] int i
  = "atslib_fgetc_err"
// end of [fgetc1_err]

symintr fgetc_err
overload fgetc_err with fgetc0_err
overload fgetc_err with fgetc1_err

// ------------------------------------------------

(*

// int fgetpos(FILE *stream, fpos_t *pos);

The [fgetpos] function stores the file position indicator of the given file
stream in the given position variable. The position variable is of type
fpos_t (which is defined in stdio.h) and is an object that can hold every
possible position in a FILE. [fgetpos] returns zero upon success, and a
non-zero value upon failure.

*)

abst@ype fpos_t = $extype "ats_fpos_type"

dataview fgetpos_v (addr, int) =
  | {l:addr} fgetpos_v_succ (l, 0) of fpos_t @ l
  | {l:addr} {i:int | i < 0} fgetpos_v_fail (l, i) of fpos_t? @ l
// end of [fgetpos_v]

fun fgetpos {m:fm} {l_pos:addr}
  (pf: fpos_t? @ l_pos | f: &FILE m, p: ptr l_pos)
  :<> [i:int | i <= 0] (fgetpos_v (l_pos, i) | int i)
  = "atslib_fgetpos"
// end of [fgetpos]

// ------------------------------------------------

(*

// char *fgets (char *str, int size, FILE *stream);

[fgets] reads in at most one less than [size] characters from stream and
stores them into the buffer pointed to by s.  Reading stops after an EOF or
a newline.  If a newline is read, it is stored into the buffer.  A '\0' is
stored after the last character in the buffer.

*)

dataview
fgets_v (sz:int, addr, addr) =
  | {l_buf:addr}
    fgets_v_fail (sz, l_buf, null) of b0ytes (sz) @ l_buf
  | {n:nat | n < sz} {l_buf:addr | l_buf <> null}
    fgets_v_succ (sz, l_buf, l_buf) of strbuf (sz, n) @ l_buf
// end of [fgets_v]

fun fgets_err
  {n,sz:int | 0 < n; n <= sz} {m:fm} {l_buf:addr} (
    pf_mod: file_mode_lte (m, r)
  , pf_buf: b0ytes (sz) @ l_buf
  | p: ptr l_buf, n: int n, f: &FILE m
  ) :<> [l:addr] (fgets_v (sz, l_buf, l) | ptr l)
  = "atslib_fgets_err"
// end of [fgets_err]

//
// this function returns an empty strbuf in the case where
// EOF is reached but no character is read
//
fun fgets_exn
  {n0,sz:int | 0 < n0; n0 <= sz}
  {m:fm} {l_buf:addr} (
    pf_mod: file_mode_lte (m, r),
    pf_buf: !b0ytes (sz) @ l_buf >>
     [n:nat | n < n0] strbuf (sz, n) @ l_buf
  | p: ptr l_buf, n0: int n0, f: &FILE m
  ) :<!exn> void = "atslib_fgets_exn"
// end of [fgets_exn]

// ------------------------------------------------

(*
 
The function fileno examines the argument stream and returns its integer
descriptor. In case fileno detects that its argument is not a valid stream,
it must return -1 and set errno to EBADF.

*)

(* the type of the function indicates that it should not fail! *)

fun fileno0 (f: FILEref):<> int = "atslib_fileno"
fun fileno1 {m:fm} (f: &FILE m):<> int = "atslib_fileno"

symintr fileno
overload fileno with fileno0
overload fileno with fileno1

// ------------------------------------------------

(*

// FILE *fopen (const char *path, const char *mode);

The fopen function opens the file whose name is the string pointed to by
path and associates a stream with it.

The argument mode points to a string beginning with one of the follow
ing sequences (Additional characters may follow these sequences.):

  r      Open  text  file  for  reading.  The stream is positioned at the
         beginning of the file.

  r+     Open for reading and writing.  The stream is positioned  at  the
         beginning of the file.

  w      Truncate  file  to  zero length or create text file for writing.
         The stream is positioned at the beginning of the file.

  w+     Open for reading and writing.  The file is created  if  it  does
         not  exist, otherwise it is truncated.  The stream is positioned
         at the beginning of the file.


  a      Open for appending (writing at end of file).  The file is created
         if it does not exist.  The stream is positioned at the end of the
         file.

  a+     Open for reading and appending (writing at end  of  file).   The
         file  is created if it does not exist.  The stream is positioned
         at the end of the file.

*)

fun fopen_err {m:fm}
  (path: string, m: file_mode m):<!ref> [l:addr] (FILE_opt_v (m, l) | ptr l)
  = "atslib_fopen_err"
// end of [fopen_err]

fun fopen_exn {m:fm}
  (path: string, m: file_mode m):<!exnref> [l:addr] (FILE m @ l | ptr l)
  = "atslib_fopen_exn"
// end of [fopen_exn]

fun fopen_ref_exn {m:fm}
  (path: string, m: file_mode m):<!exnref> FILEref
  = "atslib_fopen_exn"
// end of [fopen_ref_exn]

// ------------------------------------------------

(*

// int fputc (int c, FILE *stream)

The function [fputc] writes the given character [c] to the given output
stream. The return value is the character, unless there is an error, in
which case the return value is EOF.

*)

fun fputc0_err
  (c: char, f: FILEref):<> int = "atslib_fputc_err"
// end of [fputc0_err]

fun fputc1_err {m:fm}
  (pf: file_mode_lte (m, w) | c: char, f: &FILE m)
  :<> [i:int | i <= UCHAR_MAX] int i
  = "atslib_fputc_err"

symintr fputc_err
overload fputc_err with fputc0_err
overload fputc_err with fputc1_err

//

fun fputc0_exn
  (c: char, f: FILEref):<!exn> void = "atslib_fputc_exn"
// end of [fputc0_exn]

fun fputc1_exn {m:fm}
  (pf: file_mode_lte (m, w) | c: char, f: &FILE m):<!exn> void
  = "atslib_fputc_exn"
// end of [fputc1_exn]

symintr fputc_exn
overload fputc_exn with fputc0_exn
overload fputc_exn with fputc1_exn

// ------------------------------------------------

(*

// int fputs (const char* s, FILE *stream)

The function [fputs] writes a string to a file. it returns a non-negative
number on success, or EOF on error.

*)

symintr fputs_err

fun fputs0_err
  (str: string, fil: FILEref):<> int = "atslib_fputs_err"
overload fputs_err with fputs0_err

fun fputs1_err {m:fm}
  (pf: file_mode_lte (m, w) | str: string, f: &FILE m):<> int
  = "atslib_fputs_err"
overload fputs_err with fputs1_err

fun fputs0_exn
  (str: string, fil: FILEref):<!exn> void = "atslib_fputs_exn"
// end of [fputs0_exn]

fun fputs1_exn {m:fm}
  (pf: file_mode_lte (m, w) | str: string, f: &FILE m):<!exn> void
  = "atslib_fputs_exn"
// end of [fputs1_exn]

symintr fputs_exn
overload fputs_exn with fputs0_exn
overload fputs_exn with fputs1_exn

// ------------------------------------------------

(*

// size_t fread (void *ptr, size_t size, size_t nmemb, FILE *stream);

The function [fread] reads [nmemb] elements of data, each [size] bytes
long, from the stream pointed to by stream, storing them at the location
given by ptr. The return value is the number of items that are actually
read.

[fread] does not distinguish between end-of-file and error, and callers
must use [feof] and [ferror] to determine which occurred.

*)

fun fread
  {sz:pos} {n_buf:int}
  {n,nsz:nat | nsz <= n_buf} {m:fm} (
    pf_mod: file_mode_lte (m, r)
  , pf_mul: MUL (n, sz, nsz)
  | buf: &bytes (n_buf)
  , sz: size_t sz, n: size_t n
  , f: &FILE m
  ) :<> sizeLte n = "atslib_fread"
// end of [fread]

fun fread_byte
  {n_buf:int} {n:nat | n <= n_buf} {m:fm} (
    pf_mod: file_mode_lte (m, r) | buf: &bytes (n_buf), n: size_t n, f: &FILE m
  ) :<> sizeLte n = "atslib_fread_byte"
// end of [fread_byte]

fun fread_byte_exn
  {n_buf:int} {n:nat | n <= n_buf} {m:fm} (
    pf_mod: file_mode_lte (m, r) | buf: &bytes (n_buf), n: size_t n, f: &FILE m
  ) :<!exn> void = "atslib_fread_byte_exn"
// end of [fread_byte_exn]

// ------------------------------------------------

(*

// FILE *freopen (const char *path, const char *mode, FILE *stream);

The [freopen] function opens the file whose name is the string pointed to by
path and associates the stream pointed to by stream with it.  The original
stream (if it exists) is closed.  The mode argument is used just as in the
fopen function.  The primary use of the freopen function is to change the
file associated with a standard text stream (stderr, stdin, or stdout).

*)

symintr freopen_err

fun freopen0_err {m_new:fm}
  (path: string, m_new: file_mode m_new, f: FILEref):<!ref> void
  = "atslib_freopen_err"
overload freopen_err with freopen0_err

fun freopen1_err {m_old,m_new:fm} {l_file:addr}
  (pf: FILE m_old @ l_file | s: string, m: file_mode m_new, p: ptr l_file)
  :<!ref> [l:addr | l == null || l == l_file] (FILE_opt_v (m_new, l) | ptr l)
  = "atslib_freopen_err"
overload freopen_err with freopen1_err

//

symintr freopen_exn

fun freopen0_exn {m_new:fm}
  (path: string, m_new: file_mode m_new, f: FILEref):<!exnref> void
  = "atslib_freopen_exn"
overload freopen_exn with freopen0_exn

fun freopen1_exn {m_old,m_new:fm} {l_file:addr}
  (pf: FILE m_old @ l_file | path: string, m: file_mode m_new, p: ptr l_file)
  :<!exnref> (FILE m_new @ l_file | void)
  = "atslib_freopen_exn"
overload freopen_exn with freopen1_exn

//

fun freopen_stdin {m:fm}
  (s: string):<!exnref> void = "atslib_freopen_stdin"
// end of [freopen_stdin]

fun freopen_stdout {m:fm}
  (s: string):<!exnref> void = "atslib_freopen_stdout"
// end of [freopen_stdout]

fun freopen_stderr {m:fm}
  (s: string):<!exnref> void = "atslib_freopen_stderr"
// end of [freopen_stderr]

// ------------------------------------------------

(*

// int fseek (FILE *stream, long offset, int whence)

The [fseek] function sets the file position indicator for the stream
pointed to by stream.  The new position, measured in bytes, is obtained by
adding offset bytes to the position specified by whence.  If whence is set
to [SEEK_SET], [SEEK_CUR], or [SEEK_END], the offset is relative to the
start of the file, the current position indicator, or end-of-file,
respectively.  A successful call to the [fseek] function clears the end-
of-file indicator for the stream and undoes any effects of the [ungetc]
function on the same stream. Upon success, [fseek] returns 0. Otherwise,
it returns -1.

*)

symintr fseek_err

fun fseek0_err
  (f: FILEref, offset: lint, whence: whence_t):<> int = "atslib_fseek_err"
overload fseek_err with fseek0_err

fun fseek1_err {m:fm}
  (f: &FILE m, offset: lint, whence: whence_t):<> int = "atslib_fseek_err"
overload fseek_err with fseek1_err

//

symintr fseek_exn

fun fseek0_exn
  (f: FILEref, offset: lint, whence: whence_t):<!exn> void = "atslib_fseek_exn"
overload fseek_exn with fseek0_exn

fun fseek1_exn {m:fm}
  (f: &FILE m, offset: lint, whence: whence_t):<!exn> void = "atslib_fseek_exn"
overload fseek_exn with fseek1_exn

// ------------------------------------------------

(*

// void fsetpos(FILE *stream, const fpos_t *pos);

The [fsetpos] function moves the file position indicator for the given
stream to a location specified by the position object. The type fpos_t is
defined in stdio.h.  The return value for fsetpos() is zero upon success,
non-zero on failure.

*)

fun fsetpos {m:fm} (f: &FILE m, pos: &fpos_t): int = "atslib_fsetpos"

// ------------------------------------------------

(*

// long ftell (FILE *stream)

[ftell] returns the current offset of the given file stream upon on
success. Otherwise, -1 is returned and the global variable errno is set to
indicate the error.

*)

symintr ftell_err

fun ftell0_err (f: FILEref):<> lint = "atslib_ftell_err"
overload ftell_err with ftell0_err

fun ftell1_err {m:fm} (f: &FILE m):<> lint = "atslib_ftell_err"
overload ftell_err with ftell1_err

//

symintr ftell_exn

fun ftell0_exn (f: FILEref):<!exn> lint = "atslib_ftell_exn"
overload ftell_exn with ftell0_exn

fun ftell1_exn {m:fm} (f: &FILE m):<!exn> lint = "atslib_ftell_exn"
overload ftell_exn with ftell1_exn

// ------------------------------------------------

(*

// size_t fwrite (const void *ptr,  size_t size,  size_t nmemb, FILE *stream);

The function [fwrite] writes [nmemb] elements of data, each [size] bytes
long, to the stream pointed to by stream, obtaining them from the location
given by [ptr]. The return value is the number of items that are actually
written.

*)

fun fwrite // [sz]: the size of each item
  {sz:pos} {bsz:int} {n,nsz:nat | nsz <= bsz} {m:fm} (
    pf_mod: file_mode_lte (m, w), pf_mul: MUL (n, sz, nsz)
  | buf: &bytes (bsz), sz: size_t sz, n: size_t n, fil: &FILE m
  ) :<> natLte n
  = "atslib_fwrite"

// [fwrite_byte] is a special case of [fwrite]
fun fwrite_byte // [fwrite_byte] only writes once
  {bsz:int} {n:nat | n <= bsz} {m:fm} (
    pf_mod: file_mode_lte (m, w) | buf: &bytes (bsz), n: size_t n, fil: &FILE m
  ) :<> sizeLte n
  = "atslib_fwrite_byte"

// an uncatchable exception is thrown if not all bytes are written
fun fwrite_byte_exn
  {bsz:int} {n:nat | n <= bsz} {m:fm} (
    pf_mod: file_mode_lte (m, w) | buf: &bytes (bsz), n: size_t n, fil: &FILE m
  ) :<!exn> void
  = "atslib_fwrite_byte_exn"

(*

// perror - print a system error message

The routine [perror(s)] produces a message on the standard error output,
describing the last error encountered during a call to a system or library
function.  First (if s is not NULL and *s is not NULL) the argument string
s is printed, followed by a colon and a blank.  Then the message and a
newline.

*)

fun perror (msg: string):<> void = "atslib_perror"

// ------------------------------------------------

macdef getc = fgetc_err
macdef putc = fputc_err

// ------------------------------------------------

fun getchar ():<> int = "atslib_getchar"
fun getchar1 ():<> [i:int | i <= UCHAR_MAX] int i
  = "atslib_getchar"

fun putchar (c: char):<> int = "atslib_putchar"
fun putchar1 (c: char):<> [i:int | i <= UCHAR_MAX] int i
  = "atslib_putchar"

// ------------------------------------------------

// [puts] puts a newline at the end
fun puts_err (s: string):<> int = "atslib_puts_err"
fun puts_exn (s: string):<!exn> void = "atslib_puts_exn"

// ------------------------------------------------

fun remove_err (s: string):<!ref> int = "atslib_remove_err"
fun remove_exn (s: string):<!exnref> void = "atslib_remove_exn"

fun rename_err (oldpath: string, newpath: string):<!ref> int
  = "atslib_rename_err"
fun rename_exn (oldpath: string, newpath: string):<!exnref> void
  = "atslib_rename_exn"

// ------------------------------------------------

// [rewind] generates no error
fun rewind0 {m:fm} (fil: FILEref):<> void = "atslib_rewind"
fun rewind1 {m:fm} (fil: &FILE m):<> void = "atslib_rewind"

symintr rewind
overload rewind with rewind0
overload rewind with rewind1

// ------------------------------------------------

fun tmpfile_err
  () :<!ref> [l:addr] (FILE_opt_v (rw, l) | ptr l) = "atslib_tmpfile_err"
// end of [tmpfile_err]

fun tmpfile_exn
  () :<!exnref> [l:addr] (FILE_v (rw, l) | ptr l) = "atslib_tmpfile_exn"
// end of [tmpfile_exn]

fun tmpfile_ref_exn ():<!exnref> FILEref = "atslib_tmpfile_exn"

(*

// int ungetc(int c, FILE *stream);

[ungetc] pushes [c] back to stream, cast to unsigned char, where it is
available for subsequent read operations.  Pushed-back characters will be
returned in reverse order; only one pushback is guaranteed.

*)

fun ungetc0_err
  (c: char, f: FILEref):<> int = "atslib_ungetc_err"
// end of [ungetc0_err]

fun ungetc1_err {m:fm}
  (c: char, f: &FILE m):<> [i:int | i <= UCHAR_MAX] int i
  = "atslib_ungetc_err"
// end of [ungetc1_err]

symintr ungetc_err
overload ungetc_err with ungetc0_err
overload ungetc_err with ungetc1_err

//

fun ungetc0_exn (c: char, f: FILEref):<!exn> void
  = "atslib_ungetc_exn"

fun ungetc1_exn {m:fm} (c: char, f: &FILE m):<!exn> void
  = "atslib_ungetc_exn"

symintr ungetc_exn
overload ungetc_exn with ungetc0_exn
overload ungetc_exn with ungetc1_exn

// ------------------------------------------------

(* end of [stdio.sats] *)
