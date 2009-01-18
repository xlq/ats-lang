// A simple web server implemented in ATS

//
// This is a simple example demonstrating some use of views in
// socket programming. The code is largely based on an earlier
// version by Rui Shi (shearer AT cs DOT bu DOT edu)
//
// Note that this is not really a robust implmentation as there
// are clearly memory leaks!
//

// June 2007:
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)

%{^

#include <signal.h>
#include <sys/stat.h>

%}

//

staload "libc/SATS/dirent.sats"
staload "libc/SATS/stdio.sats"
staload "libc/netinet/SATS/in.sats"
staload "libc/sys/SATS/socket.sats"

//

#define BUFSZ 1024
#define BACKLOG 5

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

//

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
)

in

stavar len: int

prval () = free_gc_elim (pf_gc)
val (the_doctype_map_prop | ()) = vbox_make_view_ptr (pf_arr | ptr)
val the_doctype_map_ptr = ptr
val the_doctype_map_len: int len = len

end // end of [local]

//

val () = let // make sure that [doctype_map] is ordered

fun aux_check_loop {n,i:nat | i <= n} {l:addr} .<n-i>.
  (pf: !array_v (@(string, string), n, l) |
   A: ptr l, n: int n, i: int i, sfx0: string):<> void =
  if i < n then let
    val sfx1 = !A.[i].0
  in
    if sfx0 < sfx1 then aux_check_loop (pf | A, n, i+1, sfx1)
    else begin $effmask_all (exit_prerrf {void}
      (1, "Internal Error: the doctype map is not ordered: %s !< %s\n", @(sfx0, sfx1))
    ) end // end of [$effmask_all]
  end // end of [if]

fn aux_check {n:nat} {l:addr}
  (pf: !array_v ((string, string), n, l) | A: ptr l, n: int n):<> void =
  if n >= 2 then
    let val sfx = !A.[0].0 in aux_check_loop (pf | A, n, 1, sfx) end
  else ()

prval vbox pf = the_doctype_map_prop

in

aux_check (pf | the_doctype_map_ptr, the_doctype_map_len)

end // end of let

//

#define s2S string1_of_string

extern fun doctype_find (sfx: string): Stropt
implement doctype_find (sfx) = let
(*
  val () = printf ("doctype_find: sfx = %s\n", @(sfx))
*)
  fun loop {i,j,n:int | 0 <= i; i <= j+1; j+1 <= n} {l:addr} .<j-i+1>.
    (pf: !array_v ((string, string), n, l) | A: ptr l, i: int i, j: int j)
    :<cloptr> Stropt =
    if i <= j then let
      val m = i + (j - i) / 2
      val key = !A.[m].0
(*
      val () = printf ("doctype_find: key = %s\n", @(key))
*)
    in
      case+ compare (key, sfx) of
      |  1 => loop (pf | A, i, m-1)
      | ~1 => loop (pf | A, m+1, j)
      |  _ (* 0 *) => stropt_some (s2S !A.[m].1)
    end else begin
      stropt_none // = null pointer
    end
  prval vbox pf = the_doctype_map_prop
in
  loop {0,len-1,len} (
    pf | the_doctype_map_ptr, 0, the_doctype_map_len - 1
  ) // end of [loop]
end // end of [doctype_find]

//

extern fun suffix_of_filename (filename: string): Stropt
implement suffix_of_filename filename = let
  val filename = s2S filename
  val i = string_index_of_char_from_right (filename, '.')
in
  if i >= 0 then let
    val n = string_length filename
    val i1 = size_of_ssize (i) + 1
  in
    stropt_some (string_make_substring (filename, i1, n-i1))
  end else begin
    stropt_none // = null pointer
  end // end of [if]
end // end of [suffix_of_filename]

//

extern fun filename_extract {n:nat}
  (msg: string n, n: size_t n): Stropt = "filename_extract"

%{$

ats_ptr_type
filename_extract(ats_ptr_type msg, ats_size_type n) {
  size_t i = 5 ;
  char *s = (char *)msg + i;
/*
  fprintf (stdout, "filename_extract: msg = %s\n", msg);
*/
  while (i < n) {
    if (*((char *)s) == ' ') break ;
    ++i ; ++s ;
  }
/*
  fprintf (stdout, "filename_extract: s = %s\n", s);
*/
  if (i > 5) { 
    return atspre_string_make_substring (msg, 5, i-5) ;
  } else {
    return (char *)0 ;
  }
}

%}

//

extern fun doctype_of_filename (filename: string): string
implement doctype_of_filename (filename: string) = let
  val sfx_opt = suffix_of_filename filename
  val dt_opt = (
    if stropt_is_none sfx_opt then
      stropt_some "text/plain" // the doctype for files without suffix
    else let
      val sfx = string_tolower (stropt_unsome sfx_opt) in doctype_find sfx
    end
  ) : Stropt
in
  if stropt_is_none dt_opt then "content/unknown"
  else stropt_unsome dt_opt
end

//

extern fun socket_write_all {fd:int} {n,sz:nat | n <= sz}
  (pf_socket: !socket_v (fd, conn) | fd: int fd, buf: &bytes sz, n: size_t n)
  : void
  = "socket_write_all"

extern fun socket_write_substring_all
  {fd:int} {i,n,sz:nat | i+n <= sz}
    (pf_socket: !socket_v (fd, conn) |
     socket_id: int fd, s: string sz, start: size_t i, n: size_t n): void
  = "socket_write_substring_all"

%{^

static inline
ats_void_type
socket_write_all(ats_int_type fd, ats_ref_type buf, ats_size_type cnt)
{
  ssize_t res ;

  while (cnt) {
    res = write(fd, buf, cnt) ;
    if (res < 0) {
      if (errno == EINTR) continue ; else return ;
    }
    if (res == 0) return ;
    buf = ((char*)buf) + res ;
    cnt = cnt - res ;
  }
  return ;
}

static inline
ats_void_type
socket_write_substring_all
  (ats_int_type fd, ats_ptr_type buf, ats_size_type start, ats_size_type cnt)
{
  socket_write_all(fd, ((char*)buf)+start, cnt) ;
  return ;
}

%}

//

val msg404_str = "\
HTTP/1.0 404 not found\r\nServer: ATS/Vanilla\r\nContent-type: text/html\r\n
<H1>The requested resource cannot be found!</H1>
"
val msg404_len = string_length msg404_str

fun msg404_send {fd:int}
  (pf_conn: !socket_v (fd, conn) | socket_id: int fd): void = 
  socket_write_substring_all (pf_conn | socket_id, msg404_str, 0, msg404_len)

//

extern fun size_of_filename (filename: string): lint = "size_of_filename"

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

fun msg200_of_filename (filename: string): string = let

val sz = size_of_filename filename
val dt = doctype_of_filename filename

in

sprintf (
"HTTP/1.0 200 OK\r\nServer: ATS/Vanilla\r\nContent-length: %li\r\nContent-type: %s\r\n\r\n",
@(sz, dt)
)

end // end of [msg200_of_filename]

fun file_send_main {fd: int}
  (pf_conn: !socket_v (fd, conn) |
   fd: int fd, file: &FILE r, filename: string): void = let

val [l_buf:addr] (pf_ngc, pf_buf | p_buf) = malloc_ngc (BUFSZ)
prval () = pf_buf := bytes_v_of_b0ytes_v (pf_buf)
val msg200_str = msg200_of_filename filename
val msg200_str = s2S msg200_str
val msg200_len = string_length msg200_str

fun aux
  (pf_conn: !socket_v (fd, conn),
   pf_buf: !bytes BUFSZ @ l_buf | fd: int fd, file: &FILE r)
  :<cloptr1> void = let
  val n = fread_byte (file_mode_lte_r_r | !p_buf, BUFSZ, file)
in
  if n > 0 then begin
    socket_write_all (pf_conn | fd, !p_buf, n);
    aux (pf_conn, pf_buf | fd, file)
  end
end // end of [aux]

in

socket_write_substring_all (pf_conn | fd, msg200_str, 0, msg200_len);
aux (pf_conn, pf_buf | fd, file);
free_ngc (pf_ngc, pf_buf | p_buf);

end // end of [file_send_main]

extern fun file_send {fd: int}
  (pf_conn: !socket_v (fd, conn) | fd: int fd, filename: string): void

implement file_send (pf_conn | fd, filename) = let

val [l_file:addr] (pf_file_opt | file) = fopen_err (filename, file_mode_r)

in

if (file <> null) then let
  prval Some_v pf_file = pf_file_opt
in
  file_send_main (pf_conn | fd, !file, filename);
  fclose_exn (pf_file | file)
end else let
  prval None_v () = pf_file_opt
in
  msg404_send (pf_conn | fd)
end // end of if

end // end of [file_send]

//

val dir_msg1_str =
  "HTTP/1.0 200 OK\nServer: ATS/Vanilla\nContent-type: text/html\n\n"

val dir_msg1_len = string_length dir_msg1_str

//

val dir_msg2_str = "<H1>\
A simple web server implemented in <A HREF=\"http://www.ats-lang.org/\">ATS</A>\
</H1>"

val dir_msg2_len = string_length dir_msg2_str

//

extern fun ctime_get (): String = "server_ctime_get"

%{^

static
ats_ptr_type server_ctime_get (void) {
  time_t t ;
  char c, *buf, *p;

  buf = ats_malloc_gc (32) ;
  time (&t) ; ctime_r (&t, buf) ; p = buf ;
  while (c = *p) {
    if (c == '\n') { *p = '\0' ; break ; }
    ++p ;
  }
  return buf ;
}

%}

val dir_msg30_str = "<pre>starting time: "
val dir_msg30_len = string_length dir_msg30_str
val dir_msg31_str = ctime_get ()
val dir_msg31_len = string_length dir_msg31_str
val dir_msg32_str = "</pre>"
val dir_msg32_len = string_length dir_msg32_str

//

extern fun dirent_name_get (dir: &DIR): Stropt = "dirent_name_get"

%{$

ats_ptr_type dirent_name_get(ats_ptr_type dir) {
  struct dirent *ent ;
  ent = readdir((DIR *)dir) ;
  if (ent) {
    return atspre_string_make_substring (ent->d_name, 0, strlen(ent->d_name)) ;
  } else {
    return (char *)0 ;
  }
}  /* end of [dirent_name_get] */ 

%}

dataviewtype entlst = entlst_nil | entlst_cons of (String, entlst)

fun entlst_append (xs0: &entlst >> entlst, ys: entlst): void =
  case+ xs0 of
  | entlst_cons (x, !xs) => (entlst_append (!xs, ys); fold@ xs0)
  | ~entlst_nil () => (xs0 := ys)

fun qsort (xs: entlst): entlst =
  case+ xs of
  | entlst_cons (!x1_r, !xs1_r) => let
      val x1 = !x1_r and xs1 = !xs1_r
    in
      part (view@ (!x1_r), view@ (!xs1_r) | xs, xs1_r, x1, xs1, entlst_nil (), entlst_nil ())
    end
  | entlst_nil () => (fold@ xs; xs)

and part {l0,l1:addr} (
    pf0: String @ l0, pf1: entlst? @ l1
  | node: entlst_cons_unfold (l0, l1)
  , node1: ptr l1, x0: String, xs: entlst, l: entlst, r: entlst
  ) : entlst = case+ xs of
  | entlst_cons (x1, !xs1_ptr) => let
      val xs1 = !xs1_ptr
    in
      if compare (x1, x0) <= 0 then
        (!xs1_ptr := l; fold@ xs; part (pf0, pf1 | node, node1, x0, xs1, xs, r))
      else
        (!xs1_ptr := r; fold@ xs; part (pf0, pf1 | node, node1, x0, xs1, l, xs))
    end // end of [entlst_cons]
  | ~entlst_nil () => let
      var l = qsort l and r = qsort r
    in
      !node1 := r; fold@ node; r := node; entlst_append (l, r); l
    end // end of [entlst_nil]

fun dirent_name_get_all (dir: &DIR): entlst = let
  fun aux (dir: &DIR, res: entlst): entlst =
    let val ent = dirent_name_get (dir) in
      if stropt_is_none ent then res else
        aux (dir, entlst_cons (stropt_unsome ent, res))
    end
  val ents = aux (dir, entlst_nil ())
in
  qsort ents
end // end of [dirent_name_get_all]

extern fun filename_type (filename: string): int = "filename_type"

%{^

ats_int_type
filename_type(ats_ptr_type filename) {
  int res ;
  struct stat buf ;
/*  
  fprintf (stdout, "filename_type: filename = %s\n", filename) ;
*/
  res = stat((char *)filename, &buf) ;
  if (res >= 0) {
    return (S_ISDIR(buf.st_mode)) ? 1 : 0 ;
  } else {
    return -1 ;
  }
}

%}

extern fun directory_send_loop {fd:int}
  (pf_conn: !socket_v (fd, conn) | fd: int fd, parent: String, ents: entlst): void

implement directory_send_loop (pf_conn | fd, parent, ents): void =
  case+ ents of
    | ~entlst_cons (ent, ents) => let
(*
        val () = printf ("directory_send_loop: parent = %s\n", @(parent))
        val () = printf ("directory_send_loop: ent = %s\n", @(ent))
*)
        val ft = case ent of
          | "." => 1 | ".." => 1 | _ => filename_type (parent + ent)
      in
        case+ ft of
        | 0 => let
            val msg = sprintf ("<A HREF=\"%s\">%s</A><BR>", @(ent, ent))
            val len = string_length msg
          in
            socket_write_substring_all (pf_conn | fd, msg, 0, len);
            directory_send_loop (pf_conn | fd, parent, ents)
          end
        | 1 => let
            val msg = tostringf ("<A HREF=\"%s/\">%s/</A><BR>", @(ent, ent))
          in
            socket_write_substring_all (pf_conn | fd, msg, 0, string_length msg);
            directory_send_loop (pf_conn | fd, parent, ents)
          end
        | _ => directory_send_loop (pf_conn | fd, parent, ents)
      end // end of [cons]
    | ~entlst_nil () => ()
// end of [directory_send_loop]

(* ****** ****** *)

extern fun directory_send {fd: int}
  (pf_conn: !socket_v (fd, conn) | fd: int fd, dirname: string): void

implement directory_send {fd}
  (pf_conn | fd, dirname): void = let
  val (pf_dir_opt | p_dir) = opendir_err(dirname)
in
  if (p_dir = null) then
    let prval None_v () = pf_dir_opt in msg404_send (pf_conn | fd) end
  else let
    prval Some_v pf_dir = pf_dir_opt
    val () = socket_write_substring_all (pf_conn | fd, dir_msg1_str, 0, dir_msg1_len)
    val () = socket_write_substring_all (pf_conn | fd, dir_msg2_str, 0, dir_msg2_len)
    val () = socket_write_substring_all (pf_conn | fd, dir_msg30_str, 0, dir_msg30_len)
    val () = socket_write_substring_all (pf_conn | fd, dir_msg31_str, 0, dir_msg31_len)
    val () = socket_write_substring_all (pf_conn | fd, dir_msg32_str, 0, dir_msg32_len)
    val dirname = s2S dirname
    val ents = dirent_name_get_all (!p_dir)
    val () = closedir_exn (pf_dir | p_dir)
  in
    directory_send_loop (pf_conn | fd, dirname, ents)
  end
end // end of [directory_send]

(* ****** ****** *)

fun request_is_get {n:nat} (s: string n): bool =
  if string_is_at_end (s, 0) then false
  else if s[0] <> 'G' then false
  else if string_is_at_end (s, 1) then false
  else if s[1] <> 'E' then false
  else if string_is_at_end (s, 2) then false
  else if s[2] <> 'T' then false
  else if string_is_at_end (s, 3) then false  
  else if s[3] <> ' ' then false
  else true

(* ****** ****** *)

extern fun main_loop_get {fd:int} {n:nat} {l_buf:addr} (
    pf_conn: socket_v (fd, conn)
  , pf_buf: !bytes BUFSZ @ l_buf
  | fd: int fd, buf: ptr l_buf, msg: string n, n: size_t n
  ) : void

implement main_loop_get (pf_conn, pf_buf | fd, buf, msg, n) = let
(*
  val () = printf ("main_loop_get: msg = %s\n", @(msg))
*)
  val name_opt = filename_extract (msg, n)
  val () =
    if stropt_is_none name_opt then
      directory_send (pf_conn | fd, "./")
    else let
      val name = stropt_unsome name_opt
      val ft = filename_type name
    in
      case+ ft of
      | 0 => file_send (pf_conn | fd, name)
      | 1 => directory_send (pf_conn | fd, name)
      | _ => msg404_send (pf_conn | fd)
    end // end of [if]
in
  socket_close_exn (pf_conn | fd)
end // end of [main_loop_get]

(* ****** ****** *)

extern fun main_loop {fd:int} {l_buf:addr}
  (pf_list: !socket_v (fd, listen), pf_buf: !bytes BUFSZ @ l_buf |
   fd: int fd, p_buf: ptr l_buf): void
   
extern fun strbuf_make_bytes
  {n:nat} {st,ln:nat | st + ln <= n}
  (buf: &bytes n, st: size_t st, ln: size_t ln)
  :<> [l:addr] (free_gc_v l, strbuf (ln+1,ln) @ l | ptr l)
  = "atspre_string_make_substring"

implement main_loop
  (pf_list, pf_buf | fd_s, p_buf): void = let
  val (pf_accept | fd_c) = accept_null_err(pf_list | fd_s)
in
  if fd_c >= 0 then let
    prval accept_succ pf_conn = pf_accept
    val n = socket_read_exn (pf_conn | fd_c, !p_buf, BUFSZ)
    val (pf_gc, pf | p) = strbuf_make_bytes (!p_buf, 0, n)
    prval () = free_gc_elim (pf_gc)
    val msg = string1_of_strbuf (pf | p)
  in
    case+ msg of // [msg] is leaked out!!!
    | _ when request_is_get (msg) => begin
        main_loop_get (pf_conn, pf_buf | fd_c, p_buf, msg, n);
        main_loop (pf_list, pf_buf | fd_s, p_buf)
      end // end of [_ when ...]
    | _ => begin
        socket_close_exn (pf_conn | fd_c);
        prerrf ("main_loop: unsupported request: %s\n", @(msg));
        main_loop (pf_list, pf_buf | fd_s, p_buf)
      end // end of [_]
  end else let
    prval accept_fail () = pf_accept
    val () = prerr "Error: [accept] failed!\n"
  in
    main_loop (pf_list, pf_buf | fd_s, p_buf)
  end
end // end of [main_loop]

(* ****** ****** *)

extern fun sigpipe_ignore (): void = "sigpipe_ignore"

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

dynload "libc/sys/DATS/socket.dats"

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
  val (pf_ngc, pf_buf | buf) = malloc_ngc (BUFSZ)
  val () = sigpipe_ignore () // prevent server crash due to broken pipe
  prval () = pf_buf := bytes_v_of_b0ytes_v (pf_buf)
  val () = main_loop(pf_sock, pf_buf | fd, buf)
  val () = socket_close_exn (pf_sock | fd)
  val () = free_ngc (pf_ngc, pf_buf | buf)
in
  // empty
end // end of [main]

(* ****** ****** *)

(* end of [server.dats] *)
