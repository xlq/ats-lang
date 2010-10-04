//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: September, 2010
//
(* ****** ****** *)
//
// book: AUP (2nd edition), pages 292 - 296
// section 5.4: Implementing a Shell (Version I)
//
(* ****** ****** *)

staload "libc/SATS/stdlib.sats" // for getenv
staload "libc/SATS/unistd.sats" // for environ_get_arrsz

(* ****** ****** *)

typedef strarr (n:int) = @[string][n]
typedef strarr0 (n:int) = @[string?][n]

dataview
getargs_v (n0:int, l:addr, int) =
  | {n:nat | n <= n0}
    getargs_v_succ (n0, l, n) of (
      strarr (n) @ l, strarr0 (n) @ l -<lin,prf> strarr0 (n0) @ l
    ) // end of [getargs_v_succ]
  | getargs_v_fail (n0, l, ~1) of (strarr0 (n0) @ l)
// end of [getargs_v]

extern
fun getargs {n0:nat} {l:addr} (
  pfargv: strarr0 (n0) @ l | pargv: ptr l, n0: int n0, iseof: &bool? >> bool
) : [n:int] (getargs_v (n0, l, n) | int n) = "#getargs"
// end of [getargs]

(* ****** ****** *)

fun printenv {n:pos} (
  argc: int n, argc: &(@[string][n])
) : void = let
  var m: size_t // uninitialized
  val (pf, fpf | p) = environ_get_arrsz (m)
  stavar m: int
  val m: size_t m = m
  var i: sizeLte m
  val _0 = size1_of_int1 (0)
  val () = for
    (i := _0; i < m; i := i+1) (printf("%s\n", @(!p.[i])))
  // end of [val]
  prval () = fpf (pf)
in
  // nothing
end // end of [printenv]

(* ****** ****** *)

%{^
void execute (
  int argc, char *argv[]
) {
  execvp (argv[0], &argv[0]) ;
  printf ("Can't execute\n") ;
  return ;
}
%} // end of [%{^]
extern
fun execute {n:pos}
  (argc: int n, argv: &(@[string][n])): void = "#execute"
// end of [execute]

implement
main () =
while (true) let
  #define MAXARG 32
  var !pargv with pfargv = @[string?][MAXARG]()
  val () = printf ("@ ", @())
  var iseof: bool // uninitialized
  val (pfargs | argc) = getargs (pfargv | pargv, MAXARG, iseof)
//
  val () = if argc >= 0 then let
    prval getargs_v_succ (pf, fpf) = pfargs
    val () = if (argc > 0) then let
      val arg0 = pargv->[0] in case+ 0 of
      | _ when arg0 = "set" => printenv (argc, !pargv)
      | _ => execute (argc, !pargv)
    end // end of [val]
    prval () = pfargv := fpf (pf)
  in
    // nothing
  end else let
    prval getargs_v_fail (pf) = pfargs
    prval () = pfargv := pf
  in
    // nothing
  end // end of [val]
//
in
  if iseof then exit (EXIT_SUCCESS)
end // end of [main]

(* ****** ****** *)

(* end of [AUP_5_4.dats] *)
