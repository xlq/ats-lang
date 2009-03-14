(*
**
** a Tiger compiler written in ATS
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: Spring, 2009
**
*)

(* ****** ****** *)

staload F = "frame.sats"

(* ****** ****** *)

staload _(*anonymous*) = "prelude/DATS/reference.dats"

(* ****** ****** *)

//
// this part is architechture-independent; it can be shared if needed
//

local

val theFraglst = ref_make_elt<$F.fraglst> (list_nil)

in // in of [loca]

implement $F.frame_theFraglst_get () = !theFraglst

implement $F.frame_theFraglst_add (frag) =
  !theFraglst := list_cons (frag, !theFraglst)
// end of [frame_theFraglst_add]

implement $F.frame_theFraglst_reset () = !theFraglst := list_nil ()
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

assume $F.access_t = access

typedef frame = '{
  frame_name= label
, frame_arglst= $F.accesslst
, frame_nlocvar= int // number of local variables in the frame
} // end of [frame]

assume $F.frame_t = frame

in // end of [in]

#define REGISTER_FP 0
#define REGISTER_RV 1

val temp_FP = $TL.temp_make_fixed (REGISTER_FP)
val exp_FP = $TREE.EXPtemp (temp_FP)

val temp_RV = $TL.temp_make_fixed (REGISTER_RV)
val exp_RV = $TREE.EXPtemp (temp_RV)

implement $F.RV = temp_RV
implement $F.FP = temp_FP
implement $F.exp_FP = exp_FP
implement $F.exp_RV = exp_RV

implement $F.exp_make_access (e_off, acc) = case+ acc of
  | InFrame (k) => begin
      $TREE.EXPmem ($TREE.EXPbinop ($TREE.PLUS, e_off, $TREE.EXPconst k))
    end // end of [InFrame]
  | InReg tmp => $TREE.EXPtemp tmp
// end of [exp_make_access]

val WORDSIZE = $F.WORDSIZE_get ()

implement $F.frame_make_new (lab, arglst) = '{
  frame_name= lab
, frame_arglst= arglst
, frame_nlocvar= 0
} where {
  fun aux
    (xs: List bool, ofs: int): List access = case+ xs of
    | list_cons (x, xs) => let
(*
        val () = begin
          prerr "frame_make_new: aux: ofs = "; prerr ofs; prerr_newline ()
        end // end of [val]
*)
        val acc = InFrame (ofs)
        val accs = aux (xs, ofs + WORDSIZE) // stack grows downard
      in
        list_cons (acc, accs)
      end // end of [list_cons]
    | list_nil () => list_nil ()
  // end of [aux]
 val arglst = aux (arglst, 0)
} // end of [frame_make_new]

implement $F.frame_name_get (f) = f.frame_name
implement $F.frame_arglst_get (f) = f.frame_arglst

extern fun frame_nlocvar_set (f: frame, n: int): void
  = "tigerats_frame_nlocvar_set"

implement $F.frame_alloc_local
  (frame, isEscaped) = case+ 0 of
  | _ when isEscaped => let
      val n = frame.frame_nlocvar
      val n_new = n - WORDSIZE // downward!
      val () = frame_nlocvar_set (frame, n_new) 
    in
      InFrame (n_new)
    end // end of [_ when ...]
  | _ (* not escaped *) => let
      val tmp = $TL.temp_make_new ()
    in
      InReg (tmp)
    end // end of [_]
// end of [frame_alloc_local]

extern typedef "frame_t" = frame

end // end of [local]

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

(* end of [frame_x86.dats] *)
