(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload TL = "templab.sats"

typedef temp = $TL.temp_t
typedef label = $TL.label_t

(* ****** ****** *)

abstype frame_t

abstype access_t
typedef accesslst = List access_t

(* ****** ****** *)

val RV : temp // return value
val FP : temp // frame pointer

(* ****** ****** *)

// [WORDSIZE} is the number of bytes in a pointer
fun WORDSIZE_get (): int = "tigerats_WORDSIZE_get"

(* ****** ****** *)

fun frame_make_new
  (lab: label, arglst: List bool(*escape status*)): frame_t

fun frame_name_get (f: frame_t): label
fun frame_arglst_get (f: frame_t): accesslst

fun frame_alloc_local (f: frame_t, isEscaped: bool): access_t

(* ****** ****** *)

staload TREE = "irtree.sats"

val exp_FP : $TREE.exp
val exp_RV : $TREE.exp

fun exp_make_access (e_off: $TREE.exp, acc: access_t): $TREE.exp

datatype frag =
  | FRAGproc of (frame_t, $TREE.stm) | FRAGstring of (label, string)
// end of [frag]

typedef fraglst = List frag

fun frame_theFraglst_get (): fraglst
fun frame_theFraglst_add (frag: frag): void
fun frame_theFraglst_reset (): void

(* ****** ****** *)

(* end of [frame.sats] *)
