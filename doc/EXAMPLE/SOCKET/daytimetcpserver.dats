//
// An introductory example to BSD Unix socket programming in ATS
//
// The following code implements a server socket that responds each request by
// sending out a string representation of the current time. This is a concurrent
// version (in contrast to an iterativet version). The use of [fork] here should
// serve as an interesting example for future reference.

// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: November, 2008

(* ****** ****** *)

staload "libc/SATS/stdio.sats"
staload "libc/SATS/time.sats"
staload "libc/sys/SATS/socket.sats"
staload "libc/netinet/SATS/in.sats"
staload "libc/arpa/SATS/inet.sats"

(* ****** ****** *)

#define LISTENQ 5 // a traditional value
#define TIME_SERVER_PORT 13000 // default value

(*

absprop forkdup_p (v: view)

extern praxi forkdup_socket
  {fd:int} {st:status} (): forkdup_p (socket_v (fd, st))

extern praxi forkdup_pair {v1,v2:view}
 (pf1: forkdup_p (v1), pf2: forkdup_p (v2)): forkdup_p @(v1, v2) 

*)

extern fun fork_cloptr_exn {v:view}
 (pf: !v | f: (v | (*none*)) -<cloptr1> void): void
 = "atslib_fork_cloptr_exn"
 
implement main (argc, argv) = let
  val nport = (if argc > 1 then int_of argv.[1] else TIME_SERVER_PORT): int
  val [fd_s:int] (pf_sock_s | fd_s) = socket_family_type_exn (AF_INET, SOCK_STREAM)
  var servaddr: sockaddr_in_struct_t // uninitialized
  val servport = in_port_nbo_of_int (nport)
  val in4addr_any = in_addr_nbo_of_hbo (INADDR_ANY)
  val () = sockaddr_ipv4_init (servaddr, AF_INET, in4addr_any, servport)
  val () = bind_ipv4_exn (pf_sock_s | fd_s, servaddr)
  val () = listen_exn (pf_sock_s | fd_s, LISTENQ) 
  val () = loop (pf_sock_s | fd_s) where {
    fun loop (pf_sock_s: !socket_v (fd_s, listen) | fd_s: int fd_s): void = let
      val [fd_c:int] (pf_sock_c | fd_c) = accept_null_exn (pf_sock_s | fd_s)
      viewdef V = @(socket_v (fd_s, listen), socket_v (fd_c, conn))
      prval pf = @(pf_sock_s, pf_sock_c)
      val f_child = lam (pf: V | (*none*)): void =<cloptr1> let
        prval @(pf_sock_s, pf_sock_c) = pf
        val () = socket_close_exn (pf_sock_s | fd_s)
        val ntick = time_get ()
        val time_str = ctime ntick // ctime is non-reentrant
        val time_str = string1_of_string0 (time_str)
        val time_str_len = string1_length (time_str)
        val _ = socket_write_substring_exn (pf_sock_c | fd_c, time_str, 0, time_str_len)
        val () = socket_close_exn (pf_sock_c | fd_c)
      in
        // empty
      end // f_child
      val () = fork_cloptr_exn {V} (pf | f_child)
      prval () = pf_sock_s := pf.0
      prval () = pf_sock_c := pf.1
      val () = socket_close_exn (pf_sock_c | fd_c)
    in
      loop (pf_sock_s | fd_s)
    end // end of [loop]
  } // end of [val]
  val () = socket_close_exn (pf_sock_s | fd_s)
in
  // empty
end // end of [main]

(* ****** ****** *)

%{

void _exit (int status) ; // declared in [unistd.h]

ats_void_type atslib_fork_cloptr_exn (ats_ptr_type f_child) {
  pid_t pid ;
  pid = fork () ;

  if (pid < 0) {
    ats_exit_errmsg (errno, "Exit: [fork] failed.\n") ;
  }

  /* this is the parent */
  if (pid > 0) { ATS_FREE (f_child) ; return ; }
  
  /* this is the child */
  ((ats_void_type (*)(ats_clo_ptr_type))((ats_clo_ptr_type)f_child)->closure_fun)(f_child) ;
  _exit (0) ; /* no need to flush STDIN, STDOUT and STDERR */
  return ; /* deadcode */
} /* end of [atslib_fork_cloptr] */

%}

(* ****** ****** *)

(* end of [daytimetcpserver.dats] *)
