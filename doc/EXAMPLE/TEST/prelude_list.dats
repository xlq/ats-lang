//
// some testing code for functions declared in
// prelude/SATS/list.sats
//

(* ****** ****** *)

staload Rand = "libc/SATS/random.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/list.dats"

(* ****** ****** *)

#define MAXELT 100
(*
fun random_list_gen {n: nat}
  (n: int n): list (natLt MAXELT, n) = loop (n, list_nil) where {
  typedef T = natLt MAXELT
  fun loop {i,j:nat} .<i>.
    (i: int i, xs: list (T, j)):<!ref> list (T, i+j) =
    if i = 0 then xs else loop (i-1, list_cons ($Rand.randint MAXELT, xs))
  // end of [loop]
} // end of [random]
*)

fun random_list_gen {n:nat}
  (n: int n): list (natLt MAXELT, n) = xs where {
  val xs = list_vt_tabulate_fun (lam _ =<!ref> $Rand.randint MAXELT, n)
  val xs = list_of_list_vt (xs)
} // end of [val]

(* ****** ****** *)

implement main (argc, argv) = let
  fn lstpr (xs: List int): void = () where {
    prval pf = unit_v ()
    val () = list_iforeach_fun {unit_v} (pf | xs, f) where {
      fn f (pf: !unit_v | i: int, x: int)
        : void = (if i > 0 then print (", "); print x)
      // end of [f]
    } // end of [val]
    prval unit_v () = pf
  } // end of [lstpr]
  val () = $Rand.srand48_with_time () // a new seed is generated
  val xs = random_list_gen (10)
//
  val () = () where {
    val () = print "xs (randomly generated) = "
    val () = lstpr (xs)
    val () = print_newline ()
  } // end of [val]
//
  val () = () where {
    val () = print "length (xs) = "
    val () = print (list_length xs)
    val () = print_newline ()
  } // end of [val]
//
  val () = () where {
    val () = print "reverse (xs) = "
    val () = lstpr (list_reverse xs)
    val () = print_newline ()
  } // end of [val]
//
  val () = () where {
    val () = print "filter (xs, evn) = "
    val () = lstpr (list_filter_fun<int> (xs, lam x =<0> x mod 2 = 0))
    val () = print_newline ()
  } // end of [val]
  val () = () where {
    val () = print "filter (xs, odd) = "
    val () = lstpr (list_filter_fun<int> (xs, lam x =<0> x mod 2 > 0))
    val () = print_newline ()
  } // end of [val]
//
  val () = () where {
    val () = print "map (xs, double) = "
    val () = lstpr (list_map_fun<int,int> (xs, lam x =<0> 2 * x))
    val () = print_newline ()
  } // end of [val]
//
  val () = () where {
    val () = print "last(xs) = "
    val () = print (list_last xs)
    val () = print_newline ()
  } // end of [val]
//
  val () = () where {
    val () = print "mergesort (xs) = "
    val () = lstpr (list_mergesort<int> (xs, lam (x1, x2, env) =<0> x1 <= x2, null))
    val () = print_newline ()
  } // end of [val]
//
  val () = () where {
    val () = print "quicksort (xs) = "
    val () = lstpr (list_quicksort<int> (xs, lam (x1, x2, env) =<0> x1 <= x2, null))
    val () = print_newline ()
  } // end of [val]
//
in
  print "The run of [prelude_list.dats] is done successfully!\n"
end // end of [main]

(* ****** ****** *)

(* end of [prelude_list.dats] *)
