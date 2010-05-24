//
// Author: Chris Double (chris.double AT double DOT co DOT nz)
// with minor modification by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
//

(* ****** ****** *)
//
// How to compile:
//   atscc -o echo_preforking echo_preforking.dats
//
// How to test:
//   1: do './echo_preforking &'
//   2: do 'telnet localhost 5000' and input a line from the keyboard
//   3: do (2) as many times as you would like to
//   4: kill the process started by 'echo_preforking' or all of its children
//
(* ****** ****** *)

staload "libc/SATS/signal.sats"
staload "libc/SATS/stdio.sats"
staload "libc/SATS/unistd.sats"
staload "libc/sys/SATS/wait.sats"
staload "libc/sys/SATS/types.sats"
staload "libc/sys/SATS/socket.sats"
staload "libc/netinet/SATS/in.sats"
staload "libc/arpa/SATS/inet.sats"

(* ****** ****** *)

staload _ = "prelude/DATS/array.dats"

(* ****** ****** *)

%{
ats_ptr_type
fdopen_exn (
  ats_int_type id, ats_ptr_type mode
) {
  FILE *fil = fdopen((int)id, (char*)mode) ;
  if (!fil) {
    perror ("fdopen") ;
    atspre_exit_prerrf (
      1, "exit(ATS): [fdopen(\"%d\", \"%s\")] failed\n", id, mode) ;
  }
  return fil ;
}
%} // end of [%{^]

(* ****** ****** *)

macdef int = int_of_pid
fun fork_child {fd:int} (
  pf_sock: !socket_v (fd,listen) |
  fd: int fd
, f: (!socket_v (fd,listen) | int fd, pid_t) -<fun1> void
) : pid_t = let
  val pid = fork_exn()
in
  if (int)pid = 0 then begin
    f (pf_sock | fd, pid); exit(0); // this is the child
  end else pid
end // end of [fork_child]

// HX: no longer needed after ATS-0.2.0:
macdef file_mode_rr = $extval (file_mode rw, "\"r+\"")
//
extern fun fchild {fd:int}
  (pf_sock: !socket_v(fd,listen) | fd: int fd, pid: pid_t):<fun1> void
implement fchild {fd} (pf_sock | fd, pid) = let
  val (pf_client | client) = accept_null_exn (pf_sock | fd)
  val (pf_fil | p_fil) = // [pf_client] gets absorbed int [pf_fil]
    fdopen (pf_client | client, file_mode_rr) where {
    extern fun fdopen {fd:int} {m:fm}
      (pf: socket_v (fd, conn) | fd: int fd, m: file_mode m)
      : [l:addr] (FILE m @ l | ptr l) = "fdopen_exn"
  } // end of [val]
  val () = fprintf (file_mode_lte_rw_w | !p_fil, "Child %d echo> ", @((int)pid))
  val () = fflush_exn(file_mode_lte_rw_w | !p_fil)
  #define BUFSZ 1024
  var !p_buf with pf_buf = @[byte][BUFSZ]() // stack allocation
  val () = fgets_exn (file_mode_lte_rw_r, pf_buf | p_buf, BUFSZ, !p_fil)
  val () = fprintf (
    file_mode_lte_rw_w | !p_fil, "%s", @(__cast p_buf)
  ) where {
    extern castfn __cast (x: ptr): string // HX: cutting a corner to save time
  } // end of [val]
  // prval () = fpf_fil (pf_fil)
  prval () = pf_buf := bytes_v_of_strbuf_v (pf_buf)
  val () = fclose_exn (pf_fil | p_fil)
  // val () = socket_close_exn (pf_client_c | client) // HX: alreay closed at this point
in
  fchild (pf_sock | fd, pid)
end // end of [fchild]

fun make_server_socket (port: int)
  : [fd:int] (socket_v(fd,listen) | int fd) = let
  val (pf_sock_s | sockfd) = socket_family_type_exn (AF_INET, SOCK_STREAM);
  var servaddr: sockaddr_in_struct_t;
  val servport = in_port_nbo_of_int (port);
  val in4addr = in_addr_nbo_of_hbo (INADDR_ANY);
  val () = sockaddr_ipv4_init (servaddr, AF_INET, in4addr, servport);
  val () = bind_ipv4_exn (pf_sock_s | sockfd, servaddr);
  val () = listen_exn (pf_sock_s | sockfd, 10);
in
  (pf_sock_s | sockfd)
end // end of [make_server_socket]

(* ****** ****** *)

implement main (argc, argv) = let
//
  var port: int = 5000 // default choice
  val () = if argc >= 2 then port := int_of (argv.[1])
  val [fd:int] (pf_sock_s | sockfd) = make_server_socket (port)
//  
  #define NCHILD 2
//
  viewdef V = socket_v(fd,listen)
  var !p_children with pf_children = @[pid_t][NCHILD]() // stack allocation
  var !p_clo = @lam ( // stack-allocated closure
    pf: !V | _: sizeLt NCHILD, x: &pid_t? >> pid_t
  ) : void =<clo> x := $effmask_all (fork_child (pf | sockfd, fchild))
  // end of [var]
  val () = array_ptr_initialize_clo_tsz {pid_t}
    (pf_sock_s | !p_children, NCHILD, !p_clo, sizeof<pid_t>)
//
  prval pfu = unit_v ()
  val () = array_ptr_foreach_fun<pid_t> {unit_v} (
    pfu
  | !p_children
  , lam (pf | pid): void => $effmask_all(printf("Forked: %d\n", @((int)pid)))
  , NCHILD
  ) // end of [val]
  prval unit_v () = pfu
//
  var status:int = 0
  viewdef V = int @ status
  var !p_clo = @lam // stack-allocated closure
    (pf: !V | pid: &pid_t): void =<clo> let
    val _pid = $effmask_all (waitpid (pid, status, WNONE))
  in
    // nothing
  end // end of [var]
  val () = array_ptr_foreach_clo<pid_t> {V} (view@ status | !p_children, !p_clo, NCHILD)
//
  val () = socket_close_exn(pf_sock_s | sockfd)
in
  // nothing
end // end of [main]

(* ****** ****** *)

(* end of [echo_preforking.dats] *)
