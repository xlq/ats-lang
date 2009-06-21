(*
** Course: Concepts of Programming Languages (BU CAS CS 320)
** Semester: Summer I, 2009
** Instructor: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
*)

//
// Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Time: June, 2009
//

(* ****** ****** *)

//
// An interpreter for STFPL (a simple typed functional programming language)
// The code was originally written by Hongwei Xi in May 2005
//

(* ****** ****** *)

staload "error.sats"
staload "symbol.sats"
staload "absyn.sats"
staload "trans1.sats"

(* ****** ****** *)

staload "interp.sats"

(* ****** ****** *)

implement fprint_v1al (out, v) = let
  macdef prstr (s) = fprint_string (out, ,(s))
in 
  case+ v of
  | V1ALbool b => begin
      prstr "V1ALbool("; fprint_bool (out, b); prstr ")"
    end // end [V1ALbool]  
  | V1ALint i => begin
     prstr "V1ALint("; fprint_int (out, i); prstr ")"
    end // end of [V1ALint]
  | V1ALclo _ => begin
      prstr "V1ALclo("; fprint_string (out, "..."); prstr ")"
    end // end of [V1ALclo]
  | V1ALstr s => begin
      prstr "V1ALstr("; fprint_string (out, s); prstr ")"
    end // end of [V1ALstr]
  | V1ALtup (vs) => begin
      prstr "V1ALtup("; fprint_v1allst (out, vs); prstr ")"
    end // end of [V1ALtup]
end // end of [fprint_v1al]

implement fprint_v1allst
  (out, vs) = loop (vs, 0) where {
  fun loop (vs: List v1al, i: int):<cloref1> void =
    case+ vs of
    | list_cons (v, vs) => loop (vs, i+1) where {
        val () = if i > 0 then fprint_string (out, ", ")
        val () = fprint_v1al (out, v)
      } // end of [list_cons]
    | list_nil () => () 
  // end of [loop]  
} // end of [fprint_v1allst]

implement print_v1al (v) = fprint_v1al (stdout_ref, v)
implement prerr_v1al (v) = fprint_v1al (stderr_ref, v)

(* ****** ****** *)

implement interp_exp (e0) = let
  #define :: list_cons; #define nil list_nil
//
  fun auxExp (env: env, e0: e1xp): v1al = begin
    case+ e0.e1xp_node of
    | E1XPann (e, t) => auxExp (env, e)
    | E1XPbool (b) => V1ALbool (b)
    | E1XPint (i) => V1ALint (i)
    | E1XPif (e1, e2, oe3) => let
        val- V1ALbool b = auxExp (env, e1)
      in
        if b then auxExp (env, e2) else begin case+ oe3 of
          | Some e3 => auxExp (env, e3) | None () => V1ALtup (nil)
        end // end of [if]
      end // end of [E1XPif]
    | E1XPopr (opr, es) => auxOpr (env, opr, es)
    | E1XPproj (e, i) => loop (vs, i) where {
        val- V1ALtup vs = auxExp (env, e)
        fun loop (vs: List v1al, i: int): v1al = let
          val- list_cons (v, vs) = vs
        in
          if i > 0 then loop (vs, i-1) else v
        end // end of [loop]
      } // end of [E1XPproj]  
    | E1XPstr (s) => V1ALstr (s)
    | E1XPtup (es) => let
        val vs = auxExp_list (env, es) in V1ALtup (vs)
      end // end of [E1XPtup]
    | _ => begin
        prerr "auxExp: not implemented"; prerr_newline (); abort (1)
      end // end of [_]
  end // end of [auxExp]    
//
  and auxExp_list (env: env, es: e1xplst): List v1al =
    case+ es of
    | list_cons (e, es) => list_cons (auxExp (env, e), auxExp_list (env, es))
    | list_nil () => list_nil ()
  (* end of [auxExp_list] *)
//
  and auxOpr
    (env: env, opr: opr, es: e1xplst): v1al = let
    val+ OPR sym = opr
    val vs = auxExp_list (env, es)
  in
    case+ 0 of
    | _ when sym = symbol_PLUS => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALint (i1 + i2)
      end // end of [_ when ...]
    | _ when sym = symbol_MINUS => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALint (i1 - i2)
      end // end of [_ when ...]
    | _ when sym = symbol_TIMES => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALint (i1 * i2)
      end // end of [_ when ...]
    | _ when sym = symbol_SLASH => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALint (i1 / i2)
      end // end of [_ when ...]
    | _ when sym = symbol_UMINUS => let
        val- V1ALint i :: _ = vs in V1ALint (~i)
      end // end of [_ when ...]
    | _ when sym = symbol_GT => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALbool (i1 > i2)
      end // end of [_ when ...]
    | _ when sym = symbol_GTE => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALbool (i1 >= i2)
      end // end of [_ when ...]
    | _ when sym = symbol_LT => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALbool (i1 < i2)
      end // end of [_ when ...]
    | _ when sym = symbol_LTE => let
        val- V1ALint i1 :: V1ALint i2 :: _ = vs
      in
        V1ALbool (i1 <= i2)
      end // end of [_ when ...]
    | _ => begin
        prerr "INTERNAL ERROR";
        prerr ": exit(STFPL): interp: auxExp: opr = "; prerr sym; prerr_newline ();
        abort {v1al} (1)
      end // end of [_]
  end // end of [auxOpr]

  val env0 = list_nil ()
in
  auxExp (env0, e0)
end // end of [interp_exp]

(* ****** ****** *)

(* end of [interp.dats] *)
