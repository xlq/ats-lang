(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

abst@ype temp_t = int64

fun temp_make_new (): temp_t
fun temp_make_fixed (n: int): temp_t

fun compare_temp_temp (_: temp_t, _: temp_t):<> Sgn
overload compare with compare_temp_temp

fun fprint_temp (out: FILEref, tmp: temp_t): void
fun print_temp (tmp: temp_t): void
fun prerr_temp (tmp: temp_t): void

(* ****** ****** *)

abstype label_t

fun label_make_new (): label_t
fun label_make_name (name: string): label_t

fun eq_label_label (_: label_t, _: label_t):<> bool
overload = with eq_label_label

fun compare_label_label (_: label_t, _: label_t):<> Sgn
overload compare with compare_label_label

fun fprint_label (out: FILEref, lab:label_t): void
fun print_label (lab: label_t): void
fun prerr_label (lab: label_t): void

(* ****** ****** *)

val tigerats_chr_lab : label_t
val tigerats_flush_lab : label_t
val tigerats_getchar_lab : label_t
val tigerats_ord_lab : label_t
val tigerats_print_lab : label_t
val tigerats_print_int_lab : label_t
val tigerats_size_lab : label_t
val tigerats_substring_lab : label_t
val tigerats_concat_lab : label_t
val tigerats_not_lab : label_t
val tigerats_exit_lab : label_t

val tigerats_main_lab : label_t
val tigerats_array_alloc_lab : label_t
val tigerats_array_make_elt_lab : label_t

val tigerats_eq_string_string_lab : label_t
val tigerats_neq_string_string_lab : label_t

(* ****** ****** *)

(* end of [templab.sats] *)
