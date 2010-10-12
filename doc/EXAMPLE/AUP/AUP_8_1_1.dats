//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: October, 2010
//
(* ****** ****** *)
//
// book: AUP (2nd edition), pages 520 - 524
// section 8.1.1: How Sockets Work
//
(* ****** ****** *)

#define SOCKETNAME "MySocket"

(* ****** ****** *)

staload "libc/SATS/errno.sats"
staload "libc/SATS/stdio.sats"
staload "libc/SATS/stdlib.sats"
staload "libc/SATS/unistd.sats"
staload "libc/sys/SATS/types.sats"

(* ****** ****** *)

staload "libc/sys/SATS/sockaddr.sats"
staload "libc/sys/SATS/socket.sats"
staload "libc/sys/SATS/un.sats"
staload "libc/sys/SATS/socket_un.sats"

(* ****** ****** *)

macdef ignore (x) = let val _ = ,(x) in (*nothing*) end

(* ****** ****** *)

extern
fun socket_write_substring
  {fd:int} {n:int} {st,ln:nat | st+ln <= n} (
    pf_sock: !socket_v (fd, conn) | fd: int fd, str: string n, st: size_t st, ln: size_t ln
  ) : void // all bytes must be written if this function returns
// end of [socket_write_substring]

implement
socket_write_substring
  {fd} {n} {st,ln}
  (pfsock | fd, str, st, ln) = let
  val (pf, fpf | p) =
    string_takeout_bufptr {n} {st} {ln} (str, st)
  val () = socket_write_all_exn (pfsock | fd, !p, ln)
  prval () = fpf (pf)
in
  // nothing
end // end of [socket_write_substring]

(* ****** ****** *)

fun print_buf_size
  {n1,n2:nat | n2 <= n1} 
  (buf: &(@[byte][n1]), n2: size_t n2): void = let
  fun loop {i:nat | i <= n2} .<n2-i>.
    (buf: &(@[byte][n1]), n2: size_t n2, i: size_t i): void =
    if i < n2 then let
      val () = print buf.[i] in loop (buf, n2, i+1)
    end // end of [if]
  // end of [loop]
in
  loop (buf, n2, 0)
end // end of [print_buf_size]

(* ****** ****** *)

implement
main () = () where {
//
  var sa: sockaddr_un
  val _err = unlink (SOCKETNAME)
  val () = sockaddr_un_init (sa, AF_UNIX, SOCKETNAME)
//
  val pid = fork_err ()
  val ipid = int_of_pid (pid)
  val () = case+ 0 of
    | _ when ipid = 0 => let // child
        var !p_buf with pf_buf = @[byte][64]()
        val [fd:int] (pfskt | fd) = socket_family_type_exn (AF_UNIX, SOCK_STREAM)
        val () = loop (pfskt | fd, sa) where {
          fun loop (
              pfskt: !socket_v (fd, init) >> socket_v (fd, conn) | fd: int fd, sa: &sockaddr_un
            ) : void = let
            prval () = sockaddr_un_trans (view@ sa)
            val (pfopt | err) = connect_err (pfskt | fd, sa, socklen_un)
            prval () = sockaddr_trans_un (view@ sa)
          in
            if err >= 0 then let
              prval connect_v_succ pf = pfopt; prval () = pfskt := pf
            in
              // nothing
            end else let
              prval connect_v_fail pf = pfopt; prval () = pfskt := pf
              val errno = errno_get ()
            in
              if (errno = ENOENT) then let
                val _ = sleep (1) in loop (pfskt | fd, sa)
              end else let
                val () = exit (EXIT_FAILURE) in loop (pfskt | fd, sa)
              end // end of [if]
            end // end of [if]
          end // end of [loop]
        } // end of [val]
        val () = socket_write_substring (pfskt | fd, "Hello!", 0, 6)
        var !p_buf with pf_buf = @[byte][64]()
        prval () = pf_buf := bytes_v_of_b0ytes_v (pf_buf)
        val nread = socket_read_exn (pfskt | fd, !p_buf, 64)        
        val () = (print "Client got: "; print_buf_size (!p_buf, nread); print_newline ())
        val () = socket_close_exn (pfskt | fd)
      in
        exit (EXIT_SUCCESS)
      end // end of [ipid = 0]
    | _ when ipid > 0 => let // parent
        val [fd:int] (pfskt | fd) = socket_family_type_exn (AF_UNIX, SOCK_STREAM)
        val () = bind_un_exn (pfskt | fd, sa)
        val () = listen_exn (pfskt | fd, SOMAXCONN)
        val (pfskt_c | fd_c) = accept_null_exn (pfskt | fd)
        var !p_buf with pf_buf = @[byte][64]()
        prval () = pf_buf := bytes_v_of_b0ytes_v (pf_buf)
        val nread = socket_read_exn (pfskt_c | fd_c, !p_buf, 64)
        val () = (print "Server got: "; print_buf_size (!p_buf, nread); print_newline ())
        val () = socket_write_substring (pfskt_c | fd_c, "Goodbye!", 0, 8)
        val () = socket_close_exn (pfskt | fd)
        val () = socket_close_exn (pfskt_c | fd_c)
      in
        exit (EXIT_SUCCESS)
      end // end of [ipid > 0]
    | _ => let
        val () = perror ("fork")
      in
        exit (EXIT_FAILURE)
      end // end of [val]
} // end of [main]

(* ****** ****** *)

(* end of [AUP_8_1_1.dats] *)
