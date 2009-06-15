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
// A parser for STFPL (a simple typed functional programming language)
// The code was originally written by Hongwei Xi in May 2005
//

(* ****** ****** *)

staload "symbol.sats"

(* ****** ****** *)

staload "absyn.sats"

(* ****** ****** *)

implement fprint_ty (out, ty) = let
  macdef prstr (s) = fprint_string (out, ,(s))
in
  case+ ty.ty_node of
  | TYbase (sym) => begin
      prstr "TYbase("; fprint_symbol (out, sym); prstr ")"
    end // end of [TYbase]   
  | TYfun (tys_arg, ty_res) => begin
      prstr "TYfun(";
      fprint_tylst (out, tys_arg); prstr "; "; fprint_ty (out, ty_res);
      prstr ")"
    end (* end of [TYfun] *)
  | TYpair (ty1, ty2) => begin
      prstr "TYpair(";
      fprint_ty (out, ty1); prstr ", "; fprint_ty (out, ty2);
      prstr ")"
    end (* end of [TYpair] *)
  | TYlist (tys) => begin
      prstr "TYlist("; fprint_tylst (out, tys); prstr ")"
    end (* end of [TYlist] *)
  | TYxVar (X) => begin
      prstr "TYxVar("; fprint_int (out, X.name); prstr ")"
    end (* end of [TYxVar] *)
end // end of [fprint_ty]

implement fprint_tylst
  (out, tys) = loop (tys, 0) where {
  fun loop (tys: tylst, i: int)
    :<cloref1> void = case+ tys of
    | list_cons (ty, tys) => loop (tys, i+1) where {
        val () = if i > 0 then fprint_string (out, ", ")
        val () = fprint_ty (out, ty)
      } // end of [list_cons]
    | list_nil () => ()
  // end of [loop]  
} (* end of [fprint_tylst] *)

(* ****** ****** *)

implement fprint_opr (out, opr) =
  case+ opr of
  | OPRplus () => fprint_string (out, "+")
  | OPRminus () => fprint_string (out, "-")
  | OPRtimes () => fprint_string (out, "*")
  | OPRslash () => fprint_string (out, "/")
  | OPRgt () => fprint_string (out, ">")
  | OPRgte () => fprint_string (out, ">=")
  | OPRlt () => fprint_string (out, "<")
  | OPRlte () => fprint_string (out, "<=")
  | OPReq () => fprint_string (out, "=")
  | OPRneq () => fprint_string (out, "<>")
  | OPRuminus () => fprint_string (out, "~") 
// end of [fprint_opr]

(* ****** ****** *)

implement fprint_e0xp (out, e0) = let
  macdef prexp (e) = fprint_e0xp (out, ,(e))
  macdef prstr (s) = fprint_string (out, ,(s))
in
  case+ e0.e0xp_node of
  | E0XPann (e, ty) => begin
      prstr "E0XPann("; prexp e; prstr "; "; fprint_ty (out, ty); prstr ")"
    end // end of [E0XPann]
  | E0XPapp (e_fun, e_arg) => begin
      prstr "E0XPapp(";
      prexp e_fun; prstr "; "; prexp e_arg;
      prstr ")"
    end // end of [E0XPapp]
  | E0XPbool b => begin
      prstr "E0XPbool("; fprint_bool (out, b); prstr ")"
    end // end of [E0XPbool] 
  | E0XPif (e_cond, e_then, e_else) => begin
      prstr "E0XPif(";
      prexp e_cond; prstr "; "; prexp e_then; prstr "; "; prexp e_else;
      prstr ")"
    end // end of [E0XPif]
  | E0XPint i => begin
      prstr "E0XPint("; fprint_int (out, i); prstr ")"
    end // end of [E0XPint]
  | E0XPlam _ => (prstr "E0XPlam("; prstr "..."; prstr ")")
  | E0XPlist es => begin
        prstr "E0XPlist("; fprint_e0xplst (out, es); prstr ")"
    end // end of [E0XPlist]    
  | E0XPfunlst _ => (prstr "E0XPfunlst("; prstr "..."; prstr ")")
  | E0XPfunsel (e, i) => begin
      prstr "E0XPfunsel("; prexp e; fprint_int (out, i); prstr ")"
    end // end of [E0XPchoose]
  | E0XPlet (sym, e_bnd, e_def) => begin
      prstr "E0XPlet(";
      fprint_symbol (out, sym); prstr "; "; prexp e_bnd; prstr "; "; prexp e_def;
      prstr ")"
    end // end of [E0XPlet]
  | E0XPopr (sym, es) => begin
      prstr "E0XPop(";
      fprint_opr (out, sym); prstr "; "; fprint_e0xplst (out, es);
      prstr ")"
    end // end of [E0XPop]
  | E0XPproj (e, i) => begin
      prstr "E0XPproj("; prexp e; fprint_int (out, i); prstr ")"
    end // end of [E0XPproj]
  | E0XPstr s => begin
      prstr "E0XPstr("; fprint_string (out, s); prstr ")"
    end // end of [E0XPstr]
  | E0XPtup es => begin
      prstr "E0XPtup("; fprint_e0xplst (out, es); prstr ")"
    end // end of [E0XPtup]
  | E0XPvar (sym) => begin
      prstr "E0XPvar("; fprint_symbol (out, sym); prstr ")"
    end // end of [E0XPvar]
(*
  | _ => ()
*)
end // end of [fprint_e0xp]

implement fprint_e0xplst
  (out, es) = loop (es, 0) where {
  fun loop (es: e0xplst, i: int)
    :<cloref1> void = case+ es of
    | list_cons (e, es) => loop (es, i+1) where {
        val () = if i > 0 then fprint_string (out, ", ")
        val () = fprint_e0xp (out, e)
      } // end of [list_cons]
    | list_nil () => ()
  // end of [loop]  
} (* end of [fprint_e0xplst] *)

(* ****** ****** *)

implement e0xp_make_ann (loc, e, t) = '{
  e0xp_loc= loc, e0xp_node= E0XPann (e, t)
} // end of [e0xp_make_ann]

implement e0xp_make_bool (loc, b) = '{
  e0xp_loc= loc, e0xp_node= E0XPbool (b)
} // end of [e0xp_make_bool]

implement e0xp_make_if (loc, e1, e2, e3) = '{
  e0xp_loc= loc, e0xp_node= E0XPif (e1, e2, e3)
} // end of [e0xp_make_if]
  
implement e0xp_make_int (loc, i) = '{
  e0xp_loc= loc, e0xp_node= E0XPint (i)
} // end of [e0xp_make_int]
  
implement e0xp_make_opr (loc, opr, es) = '{
  e0xp_loc= loc, e0xp_node= E0XPopr (opr, es)
} // end of [e0xp_make_opr]

implement e0xp_make_proj (loc, e, i) = '{
  e0xp_loc= loc, e0xp_node= E0XPproj (e, i)
} // end of [e0xp_make_proj]

implement e0xp_make_list (loc, es) = '{
  e0xp_loc= loc, e0xp_node= E0XPlist (es)
} // end of [e0xp_make_list]

implement e0xp_make_tup (loc, es) = '{
  e0xp_loc= loc, e0xp_node= E0XPtup (es)
} // end of [e0xp_make_tup]

implement e0xp_make_var (loc, sym) = '{
  e0xp_loc= loc, e0xp_node= E0XPvar (sym)
}

(* ****** ****** *)

(* end of [absyn.dats] *)
