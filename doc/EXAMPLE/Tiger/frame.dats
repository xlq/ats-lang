(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload "frame.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

//
// this part is architechture-independent; it can be shared if needed
//

local

val theFraglst = ref_make_elt<fraglst> (list_nil)

in // in of [loca]

implement frame_theFraglst_get () = !theFraglst

implement frame_theFraglst_add (frag) =
  !theFraglst := list_cons (frag, !theFraglst)
// end of [frame_theFraglst_add]

implement frame_theFraglst_reset () = !theFraglst := list_nil ()
// end of [frame_theFraglst_reset]

end // end of [local]

(* ****** ****** *)

staload TL = "templab.sats"

typedef temp = $TL.temp_t
typedef label = $TL.label_t

(* ****** ****** *)

staload  TREE = "irtree.sats"

(* ****** ****** *)

local

datatype access =
  | InFrame of int | InReg of temp
// end of [access]

assume access_t = access

typedef frame = '{
  frame_name= label
, frame_argofs= int // the difference between SP and 1st arg
, frame_arglst= accesslst
, frame_nlocvar= int // number of local variables in the frame
} // end of [frame]

assume frame_t = frame

in // end of [in]

fn fprint_access (out: FILEref, acc: access_t): void =
  case+ acc of
  | InFrame ofs => begin
      fprint_string (out, "InFrame("); fprint_int (out, ofs); fprint_string (out, ")")
    end // end of [InFrame]
  | InReg tmp => begin
      fprint_string (out, "InReg("); $TL.fprint_temp (out, tmp); fprint_string (out, ")")
    end // end of [InReg]
// end of [fprint_access]

fn prerr_access (acc: access_t): void = fprint_access (stderr_ref, acc)

implement access_is_inreg (acc) = case+ acc of InReg _ => true | _ => false
implement access_is_inframe (acc) = case+ acc of InFrame _ => true | _ => false

implement exp_make_access (e_off, acc) = case+ acc of
  | InFrame (k) => begin
      $TREE.EXPmem ($TREE.EXPbinop ($TREE.PLUS, e_off, $TREE.EXPconst k))
    end // end of [InFrame]
  | InReg tmp => $TREE.EXPtemp tmp
// end of [exp_make_access]

val WORDSIZE = WORDSIZE_get ()

(* ****** ****** *)

implement theTopFrame = let
  val lab0 = $TL.tigerats_main_lab
in
  frame_make_new (lab0, 0(*argofs*), list_nil (*arglst*))
end // end of [theTopFrame]

(* ****** ****** *)

implement frame_make_new (lab, ofs0, arglst) = '{
  frame_name= lab
, frame_argofs= ofs0
, frame_arglst= arglst
, frame_nlocvar= 0
} where {
  fun aux
    (xs: List bool, ofs: int): accesslst = case+ xs of
    | list_cons (x, xs) => let
        val acc = (
          if x(*escaped*) then InFrame (ofs) else begin
            let val tmp = $TL.temp_make_new () in InReg (tmp) end
          end // end of [if]
        ) : access
// (*
        val () = begin
          prerr "frame_make_new: aux: ofs = "; prerr ofs; prerr_newline ();
          prerr "frame_make_new: aux: acc = "; prerr_access acc; prerr_newline ();
        end // end of [val]
// *)
        // [ofs] is increased regardless [acc] is InFrame or InReg
        val accs = aux (xs, ofs + WORDSIZE) // stack grows downward
      in
        list_cons (acc, accs)
      end // end of [list_cons]
    | list_nil () => list_nil ()
  // end of [aux]
 val arglst = aux (arglst, ofs0)
} // end of [frame_make_new]

implement frame_name_get (f) = f.frame_name
implement frame_argofs_get (f) = f.frame_argofs
implement frame_arglst_get (f) = f.frame_arglst

extern fun frame_nlocvar_set (f: frame, n: int): void
  = "tigerats_frame_nlocvar_set"

implement frame_alloc_local
  (frame, isEscaped) = case+ 0 of
  | _ when isEscaped => let
      val n = frame.frame_nlocvar
      val n_new = n - WORDSIZE // downward!
      val () = frame_nlocvar_set (frame, n_new) 
    in
      InFrame (n_new)
    end // end of [_ when ...]
  | _ (* not escaped *) => let
      val tmp = $TL.temp_make_new () in InReg (tmp)
    end // end of [_]
// end of [frame_alloc_local]

extern typedef "frame_t" = frame

end // end of [local]

(* ****** ****** *)

#include "params.hats"

(* ****** ****** *)

#if (MARCH == "MIPS") #then

// tmp0 (*SP*) -> r29
// tmp1 (*FP*) -> r30
// tmp2 (*RV*) -> r2 (* or r3 *)
// tmp3 (*RA*) -> r31

#define REGISTER_SP 0
#define REGISTER_FP 1
#define REGISTER_RV 2
#define REGISTER_RA 3

val temp_SP = $TL.temp_make_fixed (REGISTER_SP)
val temp_FP = $TL.temp_make_fixed (REGISTER_FP)
val temp_RV = $TL.temp_make_fixed (REGISTER_RV)
val temp_RA = $TL.temp_make_fixed (REGISTER_RA)

implement RV = temp_RV
implement FP = temp_FP
implement SP = temp_SP

implement theSpecialReglst = '[
  temp_SP, temp_FP, temp_RV, temp_RA
] // end of [theSpecialReglst]

implement theFunargReglst = '[
  temp_r4, temp_r5, temp_r6, temp_r7
] where {
  val temp_r4 = $TL.temp_make_fixed (10)
  val temp_r5 = $TL.temp_make_fixed (11)
  val temp_r6 = $TL.temp_make_fixed (12)
  val temp_r7 = $TL.temp_make_fixed (13)
} // end of [theFunargReglst]

implement theCallersavedReglst = '[
  temp_r08, temp_r09, temp_r10, temp_r11
, temp_r12, temp_r13, temp_r14, temp_r15
, temp_r24, temp_r25
] where {
  val temp_r08 = $TL.temp_make_fixed (20)
  val temp_r09 = $TL.temp_make_fixed (21)
  val temp_r10 = $TL.temp_make_fixed (22)
  val temp_r11 = $TL.temp_make_fixed (23)
  val temp_r12 = $TL.temp_make_fixed (24)
  val temp_r13 = $TL.temp_make_fixed (25)
  val temp_r14 = $TL.temp_make_fixed (26)
  val temp_r15 = $TL.temp_make_fixed (27)
  val temp_r24 = $TL.temp_make_fixed (28)
  val temp_r25 = $TL.temp_make_fixed (29)
}

implement theCalleesavedReglst = '[
  temp_r16, temp_r17, temp_r18, temp_r19
, temp_r20, temp_r21, temp_r22, temp_r23
] where {
  val temp_r16 = $TL.temp_make_fixed (40)
  val temp_r17 = $TL.temp_make_fixed (41)
  val temp_r18 = $TL.temp_make_fixed (42)
  val temp_r19 = $TL.temp_make_fixed (43)
  val temp_r20 = $TL.temp_make_fixed (44)
  val temp_r21 = $TL.temp_make_fixed (45)
  val temp_r22 = $TL.temp_make_fixed (46)
  val temp_r23 = $TL.temp_make_fixed (47)
}

#endif

(* ****** ****** *)

#if (MARCH == "x86_32") #then

implement theFunargReglst = '[]

// tmp0 (*SP*) -> esp
// tmp1 (*FP*) -> ebp
// tmp2 (*RV*) -> eax
// tmp3 (*RA*) -> eip

#define REGISTER_SP 0
#define REGISTER_FP 1
#define REGISTER_RV 2 // tmp2 (*RV*) -> %eax
#define REGISTER_RA 3

val temp_SP = $TL.temp_make_fixed (REGISTER_SP)
val temp_FP = $TL.temp_make_fixed (REGISTER_FP)
val temp_RV = $TL.temp_make_fixed (REGISTER_RV)

implement RV = temp_RV
implement FP = temp_FP
implement SP = temp_SP

implement EAX = temp_RV
implement ESP = temp_SP
implement EBP = temp_FP

#define REGISTER_ECX 11
#define REGISTER_EDX 12

implement ECX = $TL.temp_make_fixed (REGISTER_ECX)
implement EDX = $TL.temp_make_fixed (REGISTER_EDX)

implement theCallersavedReglst = '[
  temp_eax, temp_ecx, temp_edx
] where {
  val temp_eax = EAX
  val temp_ecx = ECX
  val temp_edx = EDX
}

#define REGISTER_EBX 20
#define REGISTER_ESI 21
#define REGISTER_EDI 22

implement EBX = $TL.temp_make_fixed (REGISTER_EBX)
implement ESI = $TL.temp_make_fixed (REGISTER_ESI)
implement EDI = $TL.temp_make_fixed (REGISTER_EDI)

implement theCalleesavedReglst = '[
  temp_ebx, temp_esi, temp_edi, temp_esp, temp_ebp
] where {
  val temp_ebx = $TL.temp_make_fixed (20)
  val temp_esi = $TL.temp_make_fixed (21)
  val temp_edi = $TL.temp_make_fixed (22)
  val temp_esp = ESP
  val temp_ebp = EBP
}

#endif

(* ****** ****** *)

implement exp_FP = $TREE.EXPtemp (temp_FP)
implement exp_SP = $TREE.EXPtemp (temp_SP)
implement exp_RV = $TREE.EXPtemp (temp_RV)

(* ****** ****** *)

%{$

#define NBIT_PER_BYTE 8

ats_int_type
tigerats_WORDSIZE_get () {
  return (__WORDSIZE / NBIT_PER_BYTE) ;
}

ats_void_type
tigerats_frame_nlocvar_set
  (ats_ptr_type frame, ats_int_type n) {
  ((frame_t)frame)->atslab_frame_nlocvar = n ; return ;
} // end of [tigerats_frame_nlocvar_set]

%}

(* ****** ****** *)

(* end of [frame.dats] *)
