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

implement fprint_typ (out, t) = let
  macdef prstr (s) = fprint_string (out, ,(s))
in
  case+ t.typ_node of
  | TYPbase (sym) => begin
      prstr "TYPbase("; fprint_symbol (out, sym); prstr ")"
    end // end of [TYPbase]   
  | TYPfun (t_arg, t_res) => begin
      prstr "TYPfun(";
      fprint_typ (out, t_arg); prstr "; "; fprint_typ (out, t_res);
      prstr ")"
    end (* end of [TYPfun] *)
  | TYPtup (ts) => begin
      prstr "TYPlist("; fprint_typlst (out, ts); prstr ")"
    end (* end of [TYPlist] *)
(*
  | TYPxVar (X) => begin
      prstr "TYPxVar("; fprint_int (out, X.name); prstr ")"
    end (* end of [TYPxVar] *)
*)
end // end of [fprint_typ]

implement fprint_typlst
  (out, ts) = loop (ts, 0) where {
  fun loop (ts: typlst, i: int)
    :<cloref1> void = case+ ts of
    | list_cons (t, ts) => loop (ts, i+1) where {
        val () = if i > 0 then fprint_string (out, ", ")
        val () = fprint_typ (out, t)
      } // end of [list_cons]
    | list_nil () => ()
  // end of [loop]  
} (* end of [fprint_typlst] *)

(* ****** ****** *)

implement
  typ_make_sym (loc, sym) = '{
  typ_loc= loc, typ_node= TYPbase (sym)
} // end of [typ_make_sym]

implement
  typ_make_fun (loc, t_arg, t_res) = '{
  typ_loc= loc, typ_node= TYPfun (t_arg, t_res)
} // end of [typ_make_fun]

implement
  typ_make_tup (loc, ts) = '{
  typ_loc= loc, typ_node= TYPtup (ts)
} // end of [typ_make_list]

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

fn fprint_a0rg
  (out: FILEref, arg: a0rg): void = () where {
  val () = fprint_symbol (out, arg.a0rg_nam)
  val () = case+ arg.a0rg_typ of
    | Some typ => begin
        fprint_string (out, ": "); fprint_typ (out, typ)
      end // end of [Some]  
    | None () => ()
  // end of [val]  
} // end of [fprint_a0rg]

fn fprint_a0rglst
  (out, args) = loop (args, 0) where {
  fun loop (args: a0rglst, i: int)
    :<cloref1> void = case+ args of
    | list_cons (arg, args) => loop (args, i+1) where {
        val () = if i > 0 then fprint_string (out, ", ")
        val () = fprint_a0rg (out, arg)
      } // end of [list_cons]
    | list_nil () => ()
  // end of [loop]  
} (* end of [fprint_a0rglst] *)

(* ****** ****** *)

implement fprint_e0xp (out, e0) = let
  macdef prexp (e) = fprint_e0xp (out, ,(e))
  macdef prstr (s) = fprint_string (out, ,(s))
in
  case+ e0.e0xp_node of
  | E0XPann (e, t) => begin
      prstr "E0XPann("; prexp e; prstr "; "; fprint_typ (out, t); prstr ")"
    end // end of [E0XPann]
  | E0XPapp (e_fun, e_arg) => begin
      prstr "E0XPapp(";
      prexp e_fun; prstr "; "; prexp e_arg;
      prstr ")"
    end // end of [E0XPapp]
  | E0XPbool b => begin
      prstr "E0XPbool("; fprint_bool (out, b); prstr ")"
    end // end of [E0XPbool] 
  | E0XPfix (f, args, res, body) => begin
      prstr "E0XPfix(";
      fprint_symbol (out, f);
      prstr "; ";
      fprint_a0rglst (out, args);
      begin case+ res of
      | Some typ => (prstr "; "; fprint_typ (out, typ)) | None () => ()
      end; 
      prstr "; ";
      fprint_e0xp (out, body);
      prstr ")"
    end // end of [E0XPlam]  
  | E0XPif (e1, e2, oe3) => begin
      prstr "E0XPif(";
      prexp e1; prstr "; "; prexp e2;
      begin
        case+ oe3 of Some e3 => (prstr "; "; prexp e3) | None () => ()
      end;
      prstr ")"
    end // end of [E0XPif]
  | E0XPint i => begin
      prstr "E0XPint("; fprint_int (out, i); prstr ")"
    end // end of [E0XPint]
  | E0XPlam (args, res, body) => begin
      prstr "E0XPlam(";
      fprint_a0rglst (out, args);
      begin case+ res of
      | Some typ => (prstr "; "; fprint_typ (out, typ)) | None () => ()
      end; 
      prstr "; ";
      fprint_e0xp (out, body);
      prstr ")"
    end // end of [E0XPlam]  
  | E0XPlet (decs, e_body) => begin
      prstr "E0XPlet(";
      fprint_string (out, "..."); prstr "; "; prexp e_body;
      prstr ")"
    end // end of [E0XPlet]
  | E0XPopr (sym, es) => begin
      prstr "E0XPopr(";
      fprint_opr (out, sym); prstr "; "; fprint_e0xplst (out, es);
      prstr ")"
    end // end of [E0XPop]
  | E0XPproj (e, i) => begin
      prstr "E0XPproj("; prexp e; prstr "; "; fprint_int (out, i); prstr ")"
    end // end of [E0XPproj]
  | E0XPstr s => begin
      prstr "E0XPstr("; fprint_string (out, s); prstr ")"
    end // end of [E0XPstr]
  | E0XPtup es => begin
        prstr "E0XPtup("; fprint_e0xplst (out, es); prstr ")"
    end // end of [E0XPlist]    
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

implement e0xp_make_app (loc, e1, e2) = '{
  e0xp_loc= loc, e0xp_node= E0XPapp (e1, e2)
} // end of [e0xp_make_app]

implement e0xp_make_bool (loc, b) = '{
  e0xp_loc= loc, e0xp_node= E0XPbool (b)
} // end of [e0xp_make_bool]

implement e0xp_make_fix
  (loc, nam, arg, res, body) = '{
  e0xp_loc= loc, e0xp_node= E0XPfix (nam, arg, res, body)
} // end of [e0xp_make_fix]
  
implement e0xp_make_if (loc, e1, e2, oe3) = '{
  e0xp_loc= loc, e0xp_node= E0XPif (e1, e2, oe3)
} // end of [e0xp_make_if]
  
implement e0xp_make_int (loc, i) = '{
  e0xp_loc= loc, e0xp_node= E0XPint (i)
} // end of [e0xp_make_int]

implement e0xp_make_lam
  (loc, arg, res, body) = '{
  e0xp_loc= loc, e0xp_node= E0XPlam (arg, res, body)
} // end of [e0xp_make_lam]

implement e0xp_make_let
  (loc, decs, body) = '{
  e0xp_loc= loc, e0xp_node= E0XPlet (decs, body)
} // end of [e0xp_make_let]
  
implement e0xp_make_opr (loc, opr, es) = '{
  e0xp_loc= loc, e0xp_node= E0XPopr (opr, es)
} // end of [e0xp_make_opr]

implement e0xp_make_proj (loc, e, i) = '{
  e0xp_loc= loc, e0xp_node= E0XPproj (e, i)
} // end of [e0xp_make_proj]

implement e0xp_make_str (loc, str) = '{
  e0xp_loc= loc, e0xp_node= E0XPstr (str)
} // end of [e0xp_make_str]

implement e0xp_make_tup (loc, es) = '{
  e0xp_loc= loc, e0xp_node= E0XPtup (es)
} // end of [e0xp_make_list]

implement e0xp_make_var (loc, sym) = '{
  e0xp_loc= loc, e0xp_node= E0XPvar (sym)
} // end of [e0xp_make_var]

(* ****** ****** *)

implement d0ec_make_val (loc, isrec, vds) = @{
  d0ec_loc= loc, d0ec_node= D0ECval (isrec, vds)
} // end of [d0ec_make_val]

(* ****** ****** *)

(* end of [absyn.dats] *)
