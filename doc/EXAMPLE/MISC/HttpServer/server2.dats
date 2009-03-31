(*
//
// Another simple web server implemented in ATS; this one is a
// concurrent server as it forks out a process for handling each
// request. Also, it uses array-quicksort in [stdlib.h] rather
// than list-quicksort to sort directory entries.
// 

// The issue of memory leaks is taken care of here in a rather
// ad hoc manner! This example really gives a glimpse of the
// kind of difficulty involved in eliminating memory leaks!!!

//
// March 2009:
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//
*)

(* ****** ****** *)

%{^

#include <signal.h>
#include <sys/stat.h>

%}

(* ****** ****** *)

staload "libc/SATS/dirent.sats"
staload "libc/SATS/stdio.sats"
staload STDLIB = "libc/SATS/stdlib.sats"
staload "libc/SATS/string.sats"
staload "libc/SATS/time.sats"
staload "libc/SATS/unistd.sats"
staload "libc/netinet/SATS/in.sats"
staload "libc/sys/SATS/socket.sats"
staload "libc/sys/SATS/types.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/list_vt.dats"

(* ****** ****** *)

//
// I don't even know what these strings really mean :)
// I copied them from a previous implementation by Rui Shi.
//

#define HTTP_OK "200"
#define HTTP_CREATED "201"
#define HTTP_ACCEPTED "202"
#define HTTP_NOT_AUTHORITATIVE "203"
#define HTTP_NO_CONTENT "204"
#define HTTP_RESET "205"
#define HTTP_PARTIAL "206"

#define HTTP_MULT_CHOICE "300"
#define HTTP_MOVED_PERM "301"
#define HTTP_MOVED_TEMP "302"
#define HTTP_SEE_OTHER "303"
#define HTTP_NOT_MODIFIED "304"
#define HTTP_USE_PROXY "305"

#define HTTP_BAD_REQUEST "400"
#define HTTP_UNAUTHORIZED "401"
#define HTTP_PAYMENT_REQUIRED "402"
#define HTTP_FORBIDDEN "403"
#define HTTP_NOT_FOUND "404"
#define HTTP_BAD_METHOD "405"
#define HTTP_NOT_ACCEPTABLE "406"
#define HTTP_PROXY_AUTH "407"
#define HTTP_CLIENT_TIMEOUT "408"
#define HTTP_CONFLICT "409"
#define HTTP_GONE "410"
#define HTTP_LENGTH_REQUIRED "411"
#define HTTP_PRECON_FAILED "412"
#define HTTP_ENTITY_TOO_LARGE "413"
#define HTTP_REQ_TOO_LONG "414"
#define HTTP_UNSUPPORTED_TYPE "415"

(* ****** ****** *)

local

typedef string2 = @(string, string)
val (pf_gc, pf_arr | ptr, len) = $arrsz {string2} (
  ("ats",  "text/plain")
, ("au",   "audio/basic")
, ("c",    "text/plain")
, ("c++",  "text/plain")
, ("cats", "text/plain")
, ("cc",   "text/plain")
, ("dats", "text/plain")
, ("exe",  "application/octet-stream")
, ("gif",  "image/gif")
, ("h",    "text/plain")
, ("hats", "text/plain")
, ("htm",  "text/html")
, ("html", "text/html")
, ("java", "text/plain")
, ("jpeg", "image/jpeg")
, ("jpg",  "image/jpeg")
, ("ml",   "text/plain")
, ("pl",   "text/plain")
, ("ps",   "application/postscript")
, ("sats", "text/plain")
, ("sh",   "application/x-shar")
, ("sml",  "text/plain")
, ("snd",  "audio/basic")
, ("tar",  "application/x-tar")
, ("text", "text/plain")
, ("txt",  "text/plain")
, ("uu",   "application/octet-stream")
, ("wav",  "audio/x-wav")
, ("zip",  "application/zip")
) // end of [val]

stavar l: addr and n: int; typedef T = @[string2][n]

prval () = free_gc_elim (pf_gc)
val (the_doctype_map_prop | ()) = vbox_make_view_ptr {T} {l} (pf_arr | ptr)
val the_doctype_map_ptr : ptr l = ptr
val the_doctype_map_len : size_t n = size1_of_int1 (len)

val () = if the_doctype_map_len >= 2 then let
  prval vbox pf = the_doctype_map_prop
  val sfx0 = !the_doctype_map_ptr.[0].0
in
  loop (pf | the_doctype_map_ptr, the_doctype_map_len, 1, sfx0)
end where {
  fun loop {n,i:nat | i <= n} {l:addr} .<n-i>.
    (pf: !array_v (string2, n, l) | A: ptr l, n: size_t n, i: size_t i, sfx0: string)
    :<> void =
    if i < n then let
      val sfx1 = !A.[i].0 in
      if sfx0 < sfx1 then loop (pf | A, n, i+1, sfx1)
      else $effmask_all begin exit_prerrf {void}
        (1, "INTERNAL ERROR: the doctype map is not ordered: %s !< %s\n", @(sfx0, sfx1))
      end // end of [$effmask_all]
    end // end of [if]
  // end of [loop]
} // end of [val]

extern fun doctype_find (sfx: string): Stropt = "doctype_find"

in // in of [local]

//
// it is probably easier to actually implement bsearch :)
//
implement doctype_find (sfx) = let
  prval vbox pf = the_doctype_map_prop
  var key = @(sfx, nullstr) where { val nullstr = $extval (string, "0") }
  val p_arr = the_doctype_map_ptr
  val ind = $effmask_ref $STDLIB.bsearch {string2}
    (key, !p_arr, the_doctype_map_len, sizeof<string2>, cmp) where {
    val cmp = lam (x1: &string2, x2: &string2): Sgn =<0> compare (x1.0, x2.0)
  } // end of [val]
in
  if ind >= 0 then let
    val typ = string1_of_string (the_doctype_map_ptr->[ind].1) in
    stropt_some (typ)
  end else stropt_none
end // end of [doctype_find]

end // end of [local]

#define CONTENT_UNKNOWN "content/unknown"

extern fun doctype_of_filename (filename: string): string

implement doctype_of_filename (filename) = let
  val filename = string1_of_string (filename)
  val n = string1_length (filename);
  val i_dot = string_index_of_char_from_right (filename, '.')
  val dtopt = (if i_dot >= 0 then let
    val i_dot = size1_of_ssize1 (i_dot)
    val i1_dot = i_dot + 1; val ln = n - i1_dot
    var !p_buf with pf_buf = @[byte][ln+1]()
    val () = strbuf_initialize_substring (pf_buf | p_buf, filename, i1_dot, ln)
    val () = strbuf_tolower (!p_buf)
    val dtopt = doctype_find (!p_buf) where {
      extern fun doctype_find {m,n:nat} (sfx: &strbuf (m, n)): Stropt = "doctype_find"
    } // end of [val]
    prval () = pf_buf := bytes_v_of_strbuf_v (pf_buf)
  in
    dtopt
  end else begin
    stropt_none
  end) : Stropt  
in
  if stropt_is_some dtopt then stropt_unsome dtopt else CONTENT_UNKNOWN
end // end of [doctype_of_filename]

(* ****** ****** *)

local

val msg404_str = "\
HTTP/1.0 404 not found\r\nServer: ATS/Vanilla\r\nContent-type: text/html\r\n
<H1>The requested resource cannot be found!</H1>
"
val msg404_len = string1_length msg404_str

in // in of [local]

fun msg404_send {fd:int}
  (pf_conn: !socket_v (fd, conn) | socket_id: int fd): void = () where {
  val _(*n*) = socket_write_substring_exn (pf_conn | socket_id, msg404_str, 0, msg404_len)
} // end of [msg404_send]

end // end of [local]

(* ****** ****** *)

%{^

static inline
ats_lint_type
size_of_filename(ats_ptr_type filename) {
  int res ;
  struct stat buf ;
  
  res = stat((char *)filename, &buf) ;
  if (res < 0) {
    perror ("stat") ;
    atspre_exit_prerrf(1, "Exit: [stat(%s)] failed.\n", filename) ;
  }
  return buf.st_size ;
}

%}

extern fun size_of_filename (filename: string): lint = "size_of_filename"

(* ****** ****** *)

%{^

static inline
ats_void_type sigpipe_ignore () {
  int err = sigignore(SIGPIPE) ;
  if (err < 0) {
    perror("sigignore") ;
    ats_exit_errmsg (1, "Exit: [sigpipe_ignore] failed.\n") ;
  }
  return ;
}

%}

extern fun sigpipe_ignore (): void = "sigpipe_ignore"

(* ****** ****** *)

val dir_msg1_str =
  "HTTP/1.0 200 OK\nServer: ATS/Vanilla\nContent-type: text/html\n\n"

val dir_msg1_len = string_length dir_msg1_str

//

val dir_msg2_str = "<H1>\
A simple web server implemented in <A HREF=\"http://www.ats-lang.org/\">ATS</A>\
</H1>"

val dir_msg2_len = string_length dir_msg2_str

//

val dir_msg30_str = "<pre>starting time: "
val dir_msg30_len = string_length dir_msg30_str

//

val dir_msg31_str = let
  #define THIRTYTWO 32
  val (pf_gc, pf_buf | p_buf) = malloc_gc (THIRTYTWO)
  var ntick = time_get ()
  val _(*p_buf*) = ctime_r (pf_buf | ntick, p_buf) // reentrant function
  prval () = free_gc_elim (pf_gc)
in
  string1_of_strbuf1 (pf_buf | p_buf)
end // end of [val]

val dir_msg31_len = string_length dir_msg31_str

//

val dir_msg32_str = "</pre>"
val dir_msg32_len = string_length dir_msg32_str

(* ****** ****** *)

#define NMSG200 128
fn msg200_of_filename {l:addr} (
    pf: !b0ytes NMSG200 @ l >> strbuf (NMSG200, n1) @ l | p: ptr l, filename: string
  ) : #[n1:nat | n1 < NMSG200][n2:nat] int n2 = let
  val sz = size_of_filename filename; val dt = doctype_of_filename filename
in
  snprintf (pf | p, NMSG200
  , "HTTP/1.0 200 OK\r\nServer: ATS/Vanilla\r\nContent-length: %li\r\nContent-type: %s\r\n\r\n"
  , @(sz, dt)
  ) // end of [snprintf]
end // end of [msg200_of_filename]

(* ****** ****** *)

#define BUFSZ 1024

(* ****** ****** *)

fn file_send_main {fd: int} (
    pf_conn: !socket_v (fd, conn)
  | fd: int fd, file: &FILE r, filename: string
  ) : void = let
  var !p_buf with pf_buf = @[byte][BUFSZ]() // uninitialized
  prval () = pf_buf := bytes_v_of_b0ytes_v (pf_buf)
  var !p_msg with pf_msg = @[byte][NMSG200]() // uninitialized
  val msg200_str = msg200_of_filename (pf_msg | p_msg, filename)
  val msg200_len = strbuf_length (!p_msg)

  fun loop
    (pf_conn: !socket_v (fd, conn),
     pf_buf: !bytes BUFSZ @ p_buf | fd: int fd, file: &FILE r)
    :<cloptr1> void = let
    val n = fread_byte (file_mode_lte_r_r | !p_buf, BUFSZ, file)
  in
    if n > 0 then let
      val () = socket_write_loop_exn (pf_conn | fd, !p_buf, n) in
      loop (pf_conn, pf_buf | fd, file)
    end // end of [if]
  end (* end of [loop] *)
  prval () = pf_msg := bytes_v_of_strbuf_v (pf_msg)
  val () = socket_write_loop_exn (pf_conn | fd, !p_msg, msg200_len)
in
  loop (pf_conn, pf_buf | fd, file)
end // end of [file_send_main]

(* ****** ****** *)

extern fun file_send {fd: int}
  (pf_conn: !socket_v (fd, conn) | fd: int fd, filename: string): void

implement file_send (pf_conn | fd, filename) = let
  val [l_fil:addr] (pf_fil_opt | p_fil) = fopen_err (filename, file_mode_r)
in
  if (p_fil <> null) then let
    prval Some_v pf_fil = pf_fil_opt
    val () = file_send_main (pf_conn | fd, !p_fil, filename)
  in
    fclose_exn (pf_fil | p_fil)
  end else let
    prval None_v () = pf_fil_opt in msg404_send (pf_conn | fd)
  end // end of if
end // end of [file_send]

(* ****** ****** *)

fn request_is_get {m,n:nat} (buf: &strbuf (m,n)): bool =
  strncmp (str, "GET ", 4)  = 0 where {
  extern castfn __cast (p: ptr): string; val str = __cast (&buf)
} // end of [request]

(* ****** ****** *)

%{^

ats_int_type
filename_type (ats_ptr_type filename) {
  int res ;
  struct stat buf ;
/*  
  fprintf (stderr, "filename_type: filename = %s\n", filename) ;
*/
  res = stat((char *)filename, &buf) ;
  if (res >= 0) {
    return (S_ISDIR(buf.st_mode)) ? 1 : 0 ;
  } else {
    return -1 ;
  } /* end of [if] */
}

%}

extern fun filename_type (filename: string): Sgn = "filename_type"

(* ****** ****** *)

extern fun filename_extract {m,n:nat}
  (msg: &strbuf (m,n) >> strbuf (m,n1), n: size_t n): #[n1:nat] Ptr
  = "filename_extract"

%{^

ats_ptr_type
filename_extract (ats_ptr_type msg, ats_size_type n) {
  size_t i = 5 ;
  char *s0 = (char*)msg + i; char *s = s0 ;
/*
  fprintf (stderr, "filename_extract: msg = %s\n", msg);
*/
  while (i < n) {
    if (*s == ' ') { *s = '\000'; break ; }
    ++i ; ++s ;
  } // end of [while]
/*
  fprintf (stderr, "filename_extract: s = %s\n", s);
*/
  return (i > 5 ? s0 : (char*)0) ;
} /* end of [filename_extract] */

%}

(* ****** ****** *)

%{^

extern ats_ptr_type
atspre_string_make_substring
  (ats_ptr_type p0, ats_size_type st, ats_size_type ln);

ats_ptr_type dirent_name_get (ats_ptr_type dir) {
  struct dirent *ent ;
  ent = readdir((DIR *)dir) ;
  if (ent) {
    return atspre_string_make_substring (ent->d_name, 0, strlen(ent->d_name)) ;
  } else {
    return (char*)0 ;
  }
}  /* end of [dirent_name_get] */ 

%}

(*

dataview strbufopt_v (int, int, addr) =
  | {m,n:nat} strbufopt_v_none (m, n, null) of ()
  | {m,n:nat} {l:addr | l <> null}
    strbufopt_v_some (m, n, l) of (free_gc_v (m, l), strbuf_v (m, n, l))
  
viewtypedef strbufoptptr_gc
  (m:int, n:int, l:addr) = @(strbufopt_v (m, n, l) | ptr l)

*)

extern fun dirent_name_get (dir: &DIR): Stropt_gc = "dirent_name_get"

(* ****** ****** *)

viewtypedef Strlin = [m,n:nat] [l:addr] strbufptr_gc (m,n,l)

fn strbufptr_free (x: Strlin): void = let
  val (pf_gc, pf_buf | p_buf) = x in strbuf_ptr_free (pf_gc, pf_buf | p_buf)
end // end of [strbufptr_free]

(* ****** ****** *)

viewtypedef entlst = List_vt (Strlin)
viewtypedef entarrptr_gc (n: int, l:addr) =
  (free_gc_v (Strlin, n, l), @[Strlin][n] @ l | ptr l)

fun dirent_name_get_all
  (dir: &DIR, asz: &size_t 0? >> size_t n): #[n:nat][l:addr] entarrptr_gc (n, l) = let
  fun loop
    (dir: &DIR, res: entlst)
    : entlst = let
    val ent = dirent_name_get (dir) in
    if stropt_gc_is_none ent then let
      val _(*null*) = stropt_gc_unnone ent in res
    end else begin
      loop (dir, list_vt_cons (stropt_gc_unsome ent, res))
    end // end of [if]
  end // end of [loop]
  val ents = loop (dir, list_vt_nil ())
  stavar n: int
  val n: int n = list_vt_length ents
  val () = asz := size1_of_int1 (n)
  val [l:addr] (pf_gc, pf_arr | p_arr) =
    array_ptr_alloc<Strlin> (asz)
  val () = array_ptr_initialize_lst_vt<Strlin> (!p_arr, asz, ents)
  val () = $STDLIB.qsort {Strlin} {n}
     (!p_arr, asz, sizeof<Strlin>, cmp) where {
     extern castfn __cast (x: !Strlin): string; val cmp = lam 
       (x1: &Strlin, x2: &Strlin): Sgn =<fun1> compare (__cast x1, __cast x2)
  } // end of [val]  
in
  #[n | #[l | (pf_gc, pf_arr | p_arr)]]
end // end of [dirent_name_get_all]

(* ****** ****** *)

fun directory_send_loop
  {fd:int} {n:nat} {l:addr} .<n>. (
    pf_conn: !socket_v (fd, conn)
  , pf_arr: ! @[Strlin][n] @ l >> @[Strlin?][n] @ l
  | fd: int fd, parent: string, p_arr: ptr l, asz: size_t n
  ) : void = let
  #define MSGSZ 1024; viewtypedef T = Strlin
in
  if asz > 0 then let
    prval @(pf1_elt, pf2_arr) = array_v_uncons {T} (pf_arr)
    val ent = !p_arr
    val ft = let
      val str = __cast ent where {
        extern castfn __cast (ent: !Strlin): string
      } // end of [val]
    in
      case+ str of
      | "." => 1 | ".." => 1 | _ => ft where {
          val str = string1_of_string (str)
          val parent = string1_of_string (parent)
          val fil = string1_append__ptr (parent, str)
          val (pf_gc, pf_fil | p_fil) = fil
          val ft = filename_type (name) where {
            extern castfn __cast (p: ptr): string; val name = __cast p_fil
          } // end of [val]
          val () = strbuf_ptr_free (pf_gc, pf_fil | p_fil)
        } // end of [_]
    end : Sgn (* end of [val] *)
    val () = case+ 0 of
      | _ when ft >= 0 => let
          var! p_msg with pf_msg = @[byte][MSGSZ](); stadef l_msg = p_msg
          val _(*n*) : int = let
            typedef mystrbuf = [n:nat | n < MSGSZ] strbuf (MSGSZ, n)
            extern castfn __cast (ent: !Strlin): string; val str = __cast ent
          in
            case+ :(pf_msg: mystrbuf @ l_msg) => ft of
            | 0 => snprintf (
                pf_msg | p_msg, MSGSZ, "<A HREF=\"%s\">%s</A><BR>", @(str, str)
              ) // end of [0]
            | _ (* 1 *) => snprintf ( // directory
                pf_msg | p_msg, MSGSZ, "<A HREF=\"%s/\">%s/</A><BR>", @(str, str)
              ) // end of [_]
          end // end of [val]
          val () = strbufptr_free (ent)
          val len = strbuf_length !p_msg
          prval () = pf_msg := bytes_v_of_strbuf_v (pf_msg)
          val _ =  socket_write_loop_exn (pf_conn | fd, !p_msg, len)
        in
          // empty
        end // end of [0]
      | _ => strbufptr_free (ent)
    // end of [val]
    val () = directory_send_loop
      (pf_conn, pf2_arr | fd, parent, p_arr+sizeof<Strlin>, asz-1)
    prval () = pf_arr := array_v_cons {T?} (pf1_elt, pf2_arr)
  in
    // empty
  end else let
    prval () = array_v_unnil {T} (pf_arr)
    prval () = pf_arr := array_v_nil {T?} ()
  in
    // empty
  end // end of [if]
end (* end of [directory_send_loop] *)

(* ****** ****** *)

extern fun directory_send {fd: int}
  (pf_conn: !socket_v (fd, conn) | fd: int fd, dirname: string): void

implement directory_send {fd}
  (pf_conn | fd, dirname): void = let
  val (pf_dir_opt | p_dir) = opendir_err (dirname)
in
  if (p_dir = null) then
    let prval None_v () = pf_dir_opt in msg404_send (pf_conn | fd) end
  else let
    prval Some_v pf_dir = pf_dir_opt
    val _ = socket_write_substring_exn (pf_conn | fd, dir_msg1_str, 0, dir_msg1_len)
    val _ = socket_write_substring_exn (pf_conn | fd, dir_msg2_str, 0, dir_msg2_len)
    val _ = socket_write_substring_exn (pf_conn | fd, dir_msg30_str, 0, dir_msg30_len)
    val _ = socket_write_substring_exn (pf_conn | fd, dir_msg31_str, 0, dir_msg31_len)
    val _ = socket_write_substring_exn (pf_conn | fd, dir_msg32_str, 0, dir_msg32_len)
    var asz: size_t 0? // unintialized
    val (pf_gc, pf_arr | p_arr) = dirent_name_get_all (!p_dir, asz)
    val () = closedir_exn (pf_dir | p_dir)
    val () = directory_send_loop (pf_conn, pf_arr | fd, dirname, p_arr, asz)
  in
    array_ptr_free {Strlin} (pf_gc, pf_arr | p_arr)
  end // end of [if]
end (* end of [directory_send] *)

(* ****** ****** *)

extern fun main_loop_get {fd:int} {m,n:nat} {l_buf:addr} (
    pf_conn: !socket_v (fd, conn), pf_buf: !bytes BUFSZ @ l_buf
  | fd: int fd, buf: ptr l_buf, msg: &strbuf (m,n) >> strbuf (m, n1), n: size_t n
  ) : #[n1:nat] void

implement main_loop_get {fd} {m,n}
  (pf_conn, pf_buf | fd, buf, msg, n) = let
(*
  val () = begin
    prerr "main_loop_get: msg = "; prerr msg; prerr_newline ()
  end // end of [val]
*)
  val ptr = filename_extract (msg, n); val () =
    if ptr <> null then let
      val name = __filename_extract (ptr) where {
        extern castfn __filename_extract (ptr: ptr): string
      } // end of [val]
      val ft = filename_type name
    in
      case+ ft of
      | 0 => file_send (pf_conn | fd, name)
      | 1 => directory_send (pf_conn | fd, name)
      | _ => msg404_send (pf_conn | fd)
    end  else begin
      directory_send (pf_conn | fd, "./") // list the entries of
      // the current directory
    end // end of [if]
  // end of [val]
in
  // empty
end // end of [main_loop_get]

(* ****** ****** *)

extern fun main_loop {fd:int} {l_buf:addr} (
    pf_fd: socket_v (fd, listen), pf_buf: !bytes BUFSZ @ l_buf
  | fd: int fd, p_buf: ptr l_buf
  ) : void
// end of [extern]

implement main_loop
  (pf_list, pf_buf | fd_s, p_buf): void = let
  val (pf_accept | fd_c) = accept_null_err (pf_list | fd_s)
in
  if fd_c >= 0 then let
    prval accept_succ pf_conn = pf_accept
    val pid = fork_exn (); val ipid = int_of_pid (pid)
  in
    case+ 0 of
    | _ when ipid > 0 (* parent *) => let
(*
        val () = (prerr "parent: ipid = "; prerr ipid; prerr_newline ())
*)
        val () = socket_close_exn (pf_conn | fd_c)
      in
         main_loop (pf_list, pf_buf | fd_s, p_buf)
      end // end of [_ when ...]
    | _ (* child: ipid = 0 *) => let
(*
        val () = (prerr "child: ipid = "; prerr ipid; prerr_newline ())
*)
        val () = socket_close_exn (pf_list | fd_s)
        val n = socket_read_exn (pf_conn | fd_c, !p_buf, BUFSZ)
        var! p_msg with pf_msg = @[byte][n+1]()
        prval () = pf_msg := bytes_v_of_b0ytes_v pf_msg
        val _(*p_msg*) = memcpy (pf_msg | p_msg, !p_buf, n)
        val () = bytes_strbuf_trans (pf_msg | p_msg, n)
      in
        case+ 0 of
        | _ when request_is_get (!p_msg) => let
            val n = strbuf_length (!p_msg)
            val () = main_loop_get (pf_conn, pf_buf | fd_c, p_buf, !p_msg, n)
            prval () = pf_msg := bytes_v_of_strbuf_v (pf_msg)
          in
            socket_close_exn (pf_conn | fd_c)
          end // end of [_ when ...]
        | _ => let
            val () =
              prerr "main_loop: unsupported request: "
            val () = prerr_string (__cast p_msg) where {
              extern castfn __cast (p: ptr): string
            } // end of [val]
            val () = prerr_newline ()
            prval () = pf_msg := bytes_v_of_strbuf_v (pf_msg)
          in
            socket_close_exn (pf_conn | fd_c)
          end // end of [val]
      end // end of [_]
  end else let
    prval accept_fail () = pf_accept
    val () = (prerr "Error: [accept] failed!"; prerr_newline ())
  in
    main_loop (pf_list, pf_buf | fd_s, p_buf)
  end // end of [if]
end (* end of [main_loop] *)

(* ****** ****** *)

#define BACKLOG 5 // a more or less hitorically arbitrarily value

(* ****** ****** *)

dynload "libc/sys/DATS/socket.dats"

(* ****** ****** *)

implement main (argc, argv) = let
  val port = (if argc > 1 then int1_of (argv.[1]) else 8080): Int
  val () = assert_prerrf_bool1
    (port >= 1024, "The given port <%i> is not supported.\n", @(port))
  val (pf_sock | fd) = socket_family_type_exn (AF_INET, SOCK_STREAM)
  var servaddr: sockaddr_in_struct_t // uninitialized
  val servport = in_port_nbo_of_int (port)
  val in4add_any = in_addr_nbo_of_hbo (INADDR_ANY)
  val () = sockaddr_ipv4_init (servaddr, AF_INET, in4add_any, servport)
  val () = bind_ipv4_exn (pf_sock | fd, servaddr)
  val () = listen_exn (pf_sock | fd, BACKLOG)
  var! p_buf with pf_buf = @[byte][BUFSZ]()
  prval () = pf_buf := bytes_v_of_b0ytes_v (pf_buf)
  val () = sigpipe_ignore () // prevent server crash due to broken pipe
in
  main_loop (pf_sock, pf_buf | fd, p_buf)
end // end of [main]

(* ****** ****** *)

(* end of [server2.dats] *)
