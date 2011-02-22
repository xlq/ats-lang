(*
** testing some functions declared in
** contrib/linux/utils/SATS/slist.sats
*)

(* ****** ****** *)

staload UN = "prelude/SATS/unsafe.sats"

(* ****** ****** *)

staload "libats/ngc/SATS/slist.sats"
staload _(*anon*) = "libats/ngc/DATS/slist.dats"

(* ****** ****** *)

%{^
typedef
struct {
  char *name ;
  int age ;
  int sex ;
  void *next ;
} person_struct ;

ats_ptr_type
person_alloc () {
  return ATS_MALLOC(sizeof(person_struct)) ;
} // end of [person_alloc]

ats_void_type
person_free (ats_ptr_type p) { return ATS_FREE(p) ; }

ats_ptr_type
person_get_next (
  ats_ptr_type x
) {
  return ((person_struct*)x)->next ;
} // end of [person_alloc]

ats_void_type
person_set_next (
  ats_ptr_type x, ats_ptr_type p
) {
  ((person_struct*)x)->next = p ; return ;
} // end of [person_alloc]

%} // end of [%{]

(* ****** ****** *)

viewtypedef person =
$extype_struct
  "person_struct" of {
  name= strptr1, age= int, sex= int
} // end of [person]

viewtypedef personlst (n:int) = slist (person, n)

(* ****** ****** *)

extern
fun person_alloc
  : node_alloc_type (person) = "person_alloc"
implement node_alloc<person> () = person_alloc ()

(* ****** ****** *)

extern
fun person_free
  : node_free_type (person) = "person_free"
implement node_free<person> (pf | x) = person_free (pf | x)

(* ****** ****** *)

extern
fun person_get_next
  : node_get_next_type (person) = "person_get_next"
implement node_get_next<person> (pf | x) = person_get_next (pf | x)

extern
fun person_set_next
  : node_set_next_type (person) = "person_set_next"
implement node_set_next<person> (pf | x, p) = person_set_next (pf | x, p)

(* ****** ****** *)

staload "libc/SATS/random.sats"

(* ****** ****** *)

fun personlst_randgen {n:nat}
  (n: int n): personlst (n) = let
  viewtypedef a = person
in
  if n > 0 then let
//
    val (pfopt | p) = person_alloc ()
    val () = assertloc (p > null)
    prval Some_v (pfnod) = pfopt
    prval (pfat, fpfnod) = node_v_takeout_val {a?} (pfnod)
//
    val id = randint (10)
    val () = p->name := sprintf ("XYZ-%1d", @(id))
    val () = p->age := randint (100)
    val () = p->sex := randint (2)
//
    prval () = pfnod := fpfnod {a} (pfat)
//
    val xs = personlst_randgen (n-1)
  in
    slist_cons<person> (pfnod | p, xs)
  end else slist_nil ()
end // end of [personlst_randgen]

(* ****** ****** *)

implement
main () = () where {
//
  val () = srand48_with_time ()
//
  #define N 5
  val xs1 = personlst_randgen (N)
  val xs2 = personlst_randgen (N)
  val xs = slist_append<person> (xs1, xs2)
  val n = slist_length<person> (xs)
  val () = println! ("n = ", n)
  val () = assertloc ( n = N+N )
//
  val () = slist_foreach_fun<person> (xs
  , lam (x) => $effmask_all (
      printf ("%s(age=%i,sex=%i)\n", @($UN.castvwtp1 {string} (x.name), x.age, x.sex))
    )
  ) // end of [val]
//
  val xs = slist_reverse<person> (xs)
  val () = slist_foreach_fun<person> (xs
  , lam (x) => $effmask_all (
      printf ("%s(age=%i,sex=%i)\n", @($UN.castvwtp1 {string} (x.name), x.age, x.sex))
    )
  ) // end of [val]
//
  val () = slist_free_fun<person> (xs, lam (x) => strptr_free (x.name))
//
} // end of [main]

(* ****** ****** *)

(* end of [test_slist.dats] *)
