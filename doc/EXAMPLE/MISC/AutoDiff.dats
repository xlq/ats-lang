(*
**
** Automatic Differentiation
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: January, 2008
**
*)

staload "libc/SATS/math.sats"
staload LIST = "prelude/DATS/list.dats"
staload REF = "prelude/DATS/reference.dats"

datatype dualnum =
  | Base of double | Bundle of (int, dualnum, dualnum)

typedef dualnumlst (n:int) = list (dualnum, n)
typedef dualnumlst1 = dualnumlst 1
typedef dualnumlst2 = dualnumlst 2
typedef dualnumLst = [n:nat] dualnumlst (n)

(* ****** ****** *)

val zero_dualnum: dualnum = Base 0.0
val one_dualnum: dualnum = Base 1.0
val negone_dualnum: dualnum = Base (~1.0)
val two_dualnum: dualnum = Base 2.0

fn epsilon (p: dualnum): int = begin
  case+ p of Base _ => 0 | Bundle (e, _, _) => e
end // end of [epsilon]

fn primal (e: int, p: dualnum): dualnum = case+ p of
  | Base _ => p | Bundle (e1, x, _) => if e1 < e then p else x
// end of [primal]

fn perturbation (e: int, p: dualnum): dualnum = begin
  case+ p of
  | Base _ => zero_dualnum
  | Bundle (e1, _, x') => if e1 < e then zero_dualnum else x'
end // end of [perturbation]

val EPSILON = ref_make_elt<int> (0)
fn derivative (f: dualnum -<cloref1> dualnum, x: dualnum)
  : dualnum = let
  val e = !EPSILON + 1
  val () = !EPSILON := e
  val result = perturbation (e, f (Bundle (e, x, one_dualnum)))
  val () = !EPSILON := e - 1
in
  result
end // end of [derivative]

fun print_dualnum (p: dualnum): void = begin case+ p of
  | Bundle (_, x, _) => print_dualnum x | Base x => printf ("%.18g", @(x))
end // end of [print_dualnum]

fn print_dualnumlst (ps: dualnumLst): void = let
  fun aux (i: int, ps: dualnumLst): void = case+ ps of
    | list_cons (p, ps) => begin
        if i > 0 then print ", "; print_dualnum p; aux (i+1, ps)
      end
    | _ => ()
in
  aux (0, ps)
end // end of [print_dualnumlst]

(* ****** ****** *)

extern fun neg_dualnum (p: dualnum): dualnum
overload ~ with neg_dualnum

extern fun recip_dualnum (p: dualnum): dualnum

extern fun add_dualnum_dualnum (p1: dualnum, p2: dualnum): dualnum
overload + with add_dualnum_dualnum

extern fun sub_dualnum_dualnum (p1: dualnum, p2: dualnum): dualnum
overload - with sub_dualnum_dualnum

extern fun mul_dualnum_dualnum (p1: dualnum, p2: dualnum): dualnum
overload * with mul_dualnum_dualnum

extern fun div_dualnum_dualnum (p1: dualnum, p2: dualnum): dualnum
overload / with div_dualnum_dualnum

//

implement neg_dualnum (p) = case+ p of
  | Bundle (e, x, x') => Bundle (e, ~x, ~x') | Base x => Base (~x)
// end of [neg_dualnum]

//

implement add_dualnum_dualnum (p1, p2) = 
  case+ p1 of
  | Bundle (e1, x1, x1') => begin case+ p2 of
    | Bundle (e2, x2, x2') => let
        val e: int = if e1 <= e2 then e2 else e1
        val x = primal (e, p1) + primal (e, p2)
        val x' = perturbation (e, p1) + perturbation (e, p2)
      in
        Bundle (e, x, x')
      end
    | Base x2 => Bundle (e1, x1 + p2, x1')
    end
  | Base x1 => begin case+ p2 of
    | Bundle (e2, x2, x2') => Bundle (e2, p1 + x2, x2')
    | Base x2 => Base (x1 + x2)
    end
// end of [add_dualnum_dualnum]

//

implement sub_dualnum_dualnum (p1, p2) = 
  case+ p1 of
  | Bundle (e1, x1, x1') => begin case+ p2 of
    | Bundle (e2, x2, x2') => let
        val e: int = if e1 <= e2 then e2 else e1
        val x = primal (e, p1) - primal (e, p2)
        val x' = perturbation (e, p1) - perturbation (e, p2)
      in
        Bundle (e, x, x')
      end
    | Base x2 => Bundle (e1, x1 - p2, x1')
    end
  | Base x1 => begin case+ p2 of
    | Bundle (e2, x2, x2') => Bundle (e2, p1 - x2, ~x2')
    | Base x2 => Base (x1 - x2)
    end
// end of [sub_dualnum_dualnum]

//

implement mul_dualnum_dualnum (p1, p2) = 
  case+ p1 of
  | Bundle (e1, x1, x1') => begin case+ p2 of
    | Bundle (e2, x2, x2') => let
        val e: int = if e1 <= e2 then e2 else e1
        val x1 = primal (e, p1) and x2 = primal (e, p2)
        val x = x1 * x2
        val x' = x1 * perturbation (e, p2) + x2 * perturbation (e, p1)
      in
        Bundle (e, x, x')
      end
    | Base x2 => Bundle (e1, x1 * p2, p2 * x1')
    end
  | Base x1 => begin case+ p2 of
    | Bundle (e2, x2, x2') => Bundle (e2, p1 * x2, p1 * x2')
    | Base x2 => Base (x1 * x2)
    end
// end of [mul_dualnum_dualnum]

//

implement recip_dualnum (p) = case+ p of
  | Bundle (e, x, x') => Bundle (e, recip_dualnum x, (~x') / (x * x))
  | Base x => Base (1.0 / x)
// end of [recip_dualnum_dualnum]

implement div_dualnum_dualnum (p1, p2) = p1 * (recip_dualnum p2)

//

extern fun sqrt_dualnum (p: dualnum): dualnum

implement sqrt_dualnum (p) = begin case+ p of
  | Bundle (e, x, x') => let
      val x_sqrt = sqrt_dualnum x; val x'_sqrt = x' / (x_sqrt + x_sqrt)
    in
      Bundle (e, x_sqrt, x'_sqrt)
    end
  | Base x => Base (sqrt x)
end // end of [sqrt_dualnum]

//

extern fun lt_dualnum_dualnum (p1: dualnum, p2: dualnum): bool
overload < with lt_dualnum_dualnum

implement lt_dualnum_dualnum (p1, p2) = begin
  case+ p1 of
  | Bundle (_, x1, _) => begin case+ p2 of
    | Bundle (_, x2, _) => x1 < x2 | Base x2 => x1 < p2
    end
  | Base x1 => begin case+ p2 of
    | Bundle (_, x2, _) => p1 < x2 | Base x2 => x1 < x2
    end
end // end of [lt_dualnum_dualnum]

extern fun lte_dualnum_dualnum (p1: dualnum, p2: dualnum): bool
overload <= with lte_dualnum_dualnum

implement lte_dualnum_dualnum (p1, p2) = begin
  case+ p1 of
  | Bundle (_, x1, _) => begin case+ p2 of
    | Bundle (_, x2, _) => x1 <= x2 | Base x2 => x1 <= p2
    end
  | Base x1 => begin case+ p2 of
    | Bundle (_, x2, _) => p1 <= x2 | Base x2 => x1 <= x2
    end
end // end of [lte_dualnum_dualnum]

(* ****** ****** *)

fn square (p: dualnum): dualnum = p * p

fn list_tabulate {n:nat}
  (f: !natLt n -<cloptr1> dualnum, n: int n): dualnumlst n = let
  fun aux {i:int | ~1 <= i; i < n}
    (f: !natLt n -<cloptr1> dualnum, i: int i, res: list (dualnum, n-i-1))
    : list (dualnum, n) =
    if i >= 0 then aux (f, i-1, list_cons (f i, res)) else res
in
  aux (f, n-1, list_nil ())
end // end of [list_tabulate]

fun vplus {n:nat} .<n>.
  (us: dualnumlst n, vs: dualnumlst n): dualnumlst n =
  case+ us of
  | list_cons (u, us) => let
      val+ list_cons (v, vs) = vs
    in
      list_cons (u + v, vplus (us, vs))
    end
  | _ =>> list_nil ()
// end of [vplus]

fun vminus {n:nat} .<n>.
  (us: dualnumlst n, vs: dualnumlst n): dualnumlst n =
  case+ us of
  | list_cons (u, us) => let
      val+ list_cons (v, vs) = vs
    in
      list_cons (u - v, vminus (us, vs))
    end
  | _ =>> list_nil ()
// end of [vminus]

fun vscale {n:nat}
  (k: dualnum, xs: dualnumlst n): dualnumlst n =
  case+ xs of
  | list_cons (x, xs) => list_cons (k * x, vscale (k, xs))
  | list_nil () => list_nil ()
// end of [vscale]

fn magnitude_squared (xs: dualnumLst): dualnum = let
  fun aux {n:nat} .<n>.
    (xs: dualnumlst n, res: dualnum): dualnum =
    case+ xs of list_cons (x, xs) => aux (xs, res + x * x) | _ => res
in
  aux (xs, zero_dualnum)
end // end of [magnitude_squared]

fn magnitude (xs: dualnumLst): dualnum =
  sqrt_dualnum (magnitude_squared xs)

fn distance {n:nat} (us: dualnumlst n, vs: dualnumlst n): dualnum =
  magnitude (vminus (us, vs))

fun list_nth_get {n:nat} .<n>.
  (xs: dualnumlst n, i: natLt n): dualnum =
  if i > 0 then begin
    let val+ list_cons (_, xs) = xs in list_nth_get (xs, i-1) end
  end else begin
    let val+ list_cons (x, _) = xs in x end
  end
// end of [list_nth_get]

fun list_nth_set {n:nat} .<n>.
  (xs: dualnumlst n, i: natLt n, x0: dualnum): dualnumlst n =
  if i > 0 then let
    val+ list_cons (x, xs) = xs
  in
    list_cons (x, list_nth_set (xs, i-1, x0))
  end else begin
    let val+ list_cons (_, xs) = xs in list_cons (x0, xs) end
  end
// end of [list_nth_set]

fn gradient {n:nat}
  (f: dualnumlst n -<cloref1> dualnum, xs: dualnumlst n)
  : dualnumlst n = let
  fun fi (i: natLt n):<cloptr1> dualnum =
    derivative (lam xi => f (list_nth_set (xs, i, xi)), list_nth_get (xs, i))
  val gxs = list_tabulate (fi, list_length xs)
(*
  val () = begin
    print "gradient: xs = "; print_dualnumlst xs; print_newline ();
    print "gradient: gxs = "; print_dualnumlst gxs; print_newline ();
  end
*)
in
  gxs
end // end of [gradient]

val PRECISION = Base 1e-5

fn multivariate_argmin {n:nat}
  (f: dualnumlst n -<cloref1> dualnum, xs: dualnumlst n)
  : dualnumlst n = let
  fun g (xs: dualnumlst n):<cloptr1> dualnumlst n = gradient (f, xs)
  fun loop
    (xs: dualnumlst n, fxs: dualnum, gxs: dualnumlst n, eta: dualnum,i: int)
    :<cloptr1> dualnumlst n =
    if magnitude gxs <= PRECISION then xs
    else if i = 10 then loop (xs, fxs, gxs, two_dualnum * eta, 0)
    else let
      val xs' = vminus (xs, vscale (eta, gxs))
    in
      if distance (xs, xs') <= PRECISION then xs
      else let
        val fxs' = f xs'
      in
        if fxs' < fxs then loop (xs', fxs', g xs', eta, i+1)
        else loop (xs, fxs, gxs, eta / two_dualnum, 0)
      end
    end
in
  loop (xs, f xs, g xs, PRECISION, 0)
end // end of [multivariate_argmin]

fn multivariate_argmax {n:nat}
  (f: dualnumlst n -<cloref1> dualnum, xs: dualnumlst n): dualnumlst n =
  multivariate_argmin (lam xs => ~(f xs), xs)
// end of [multivariate_argmax]

fn multivariate_max {n:nat}
  (f: dualnumlst n -<cloref1> dualnum, xs: dualnumlst n): dualnum =
  f (multivariate_argmax (f, xs))
// end of [multivariate_max]

(* ****** ****** *)

fn saddle (): void = let

val start: dualnumlst2 =
  list_cons (one_dualnum, list_cons (one_dualnum, list_nil ()))

val xy1_star: dualnumlst2 = let
  fn f1 (xy1: dualnumlst2):<cloref1> dualnum = let
    val+ list_cons (x1, list_cons (y1, list_nil ())) = xy1
    val sum = x1 * x1 + y1 * y1
    fn f2 (xy2: dualnumlst2):<cloref1> dualnum = let
      val+ list_cons (x2, list_cons (y2, list_nil ())) = xy2
    in
      sum - (x2 * x2 + y2 * y2)
    end
  in
    multivariate_max (f2, start)
  end
in
  multivariate_argmin (f1, start)
end // end of [xy1_star]

val+ list_cons (x1_star, list_cons (y1_star, list_nil ())) = xy1_star

val xy2_star: dualnumlst2 = let
  val sum = x1_star * x1_star + y1_star * y1_star
  fn f3 (xy2: dualnumlst2):<cloref1> dualnum = let
    val+ list_cons (x2, list_cons (y2, list_nil ())) = xy2
  in
    sum - (x2 * x2 + y2 * y2)
  end
in
  multivariate_argmax (f3, start)
end // end of [xy2_star]

val+ list_cons (x2_star, list_cons (y2_star, list_nil ())) = xy2_star

in // in of [let]

print_dualnum x1_star; print_newline ();
print_dualnum y1_star; print_newline ();
print_dualnum x2_star; print_newline ();
print_dualnum y2_star; print_newline ();

end // end of [saddle]

(* ****** ****** *)

fn particle () = let

fn naive_euler (w: dualnum): dualnum = let
  val ten_dualnum = Base 10.0
  val delta_t = Base 1e-1
  val charge1 = '[ten_dualnum, ten_dualnum - w]
  val charge2 = '[ten_dualnum, zero_dualnum]
  val charges: list (dualnumlst2, 2) = '[charge1, charge2]
  fn p (xs: dualnumlst2):<cloref1> dualnum = let
    fun aux (charges: List dualnumlst2, res: dualnum):<cloptr1> dualnum =
      case+ charges of
      | list_cons (charge, charges) =>
          aux (charges, res + recip_dualnum (distance (xs, charge)))
      | list_nil () => res
  in
    aux (charges, zero_dualnum)
  end
  fun loop
    (xs: dualnumlst2, xs_dot: dualnumlst2):<cloptr1> dualnum = let
    val xs_ddot = vscale (negone_dualnum, gradient (p, xs))
    val xs_new = vplus (xs, vscale (delta_t, xs_dot))
  in
    if zero_dualnum < list_nth_get (xs_new, 1) then
      loop (xs_new, vplus (xs_dot, vscale (delta_t, xs_ddot)))
    else let
      val delta_t_f = ~(list_nth_get (xs, 1) / list_nth_get (xs_dot, 1))
      val xs_t_f = vplus (xs, vscale (delta_t_f, xs_dot))
    in
      square (list_nth_get (xs_t_f, 0))
    end
  end
  val xs_initial: dualnumlst2 = '[zero_dualnum, Base 8.0]
  val xs_dot_initial: dualnumlst2 = '[Base 0.75, zero_dualnum]
in
  loop (xs_initial, xs_dot_initial)
end // end [naive_euler]

val w0 = zero_dualnum
val ws_star: dualnumlst1 = multivariate_argmin (f, '[w0]) where {
  fn f (ws: dualnumlst1):<cloref1> dualnum = let
    val+ list_cons (w, list_nil ()) = ws
  in
    naive_euler w
  end
} // end of [where]

val list_cons (w_star, list_nil ()) = ws_star

in // in of [let]

print_dualnum w_star; print_newline ()

end // end of [particle]

(* ****** ****** *)

(*

// saddle: 

8.2463248261403561e-06
8.2463248261403561e-06
8.2463248261403561e-06
8.2463248261403561e-06

// particle:

0.20719187464861194

*)

implement main (argc, argv) = begin
  saddle (); // test
  particle (); // test
end // end of [main]

(* ****** ****** *)

(* end of [AutoDiff.dats] *)
