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

fun access_is_inreg (acc: access_t): bool // allocated in a reg
fun access_is_inframe (acc: access_t): bool // allocated in the frame

(* ****** ****** *)

val RV : temp // return value
val FP : temp // frame pointer
val SP : temp // stack pointer

(* ****** ****** *)

// [WORDSIZE} is the number of bytes in a pointer
fun WORDSIZE_get (): int = "tigerats_WORDSIZE_get"

(* ****** ****** *)

val theTopFrame : frame_t

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

abstype reg_t (* string *)

fun temp_reg_find (tmp: temp): Option (reg_t)

val theFunargReglst : List temp // for passing function arguments
val theSpecialReglst : List temp // for some special purposes (FP, RV, etc.)
val theCallersavedReglst : List temp // caller saved registers
val theCalleesavedReglst : List temp // callee saved registers

(* ****** ****** *)

#include "params.hats"

#if MARCH = "x86_32" #then

val EAX : temp
val EBX : temp
val ECX : temp
val EDX : temp

val ESI : temp
val EDI : temp

val ESP : temp
val EBP : temp

#endif

(* ****** ****** *)

(* end of [frame.sats] *)
