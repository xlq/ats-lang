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

staload "error.sats"

staload "PARCOMB/posloc.sats"
staload "PARCOMB/tokenize.sats"

staload "fixity.sats"

(* ****** ****** *)

staload "PARCOMB/parcomb.sats" ;
staload _(*anonymous*) = "PARCOMB/parcomb.dats" ;

(* ****** ****** *)

staload _(*anonymous*) = "prelude/SATS/file.sats" // for [stdio.cats]?

staload _(*anonymous*) = "prelude/DATS/array.dats"
staload _(*anonymous*) = "prelude/DATS/list.dats"

(* ****** ****** *)

staload "absyn.sats"
staload "symbol.sats"

(* ****** ****** *)

staload "parser.sats"

(* ****** ****** *)

infix (|| + 1) wth
infixl (&& + 2) <<; infixr (&& + 1) >>
postfix ^* ^+ ^?

(* ****** ****** *)

typedef P (a: t@ype) = parser_t (a, token)
typedef LP (a: t@ype) = lazy (parser_t (a, token))

(* ****** ****** *)

val anytoken = any_parser<token> ()
val anyopttoken = anyopt_parser<token> ()

(* ****** ****** *)

fn litchar (c0: char): P token =
  anytoken \sat (lam (tok: token): bool =<cloref>
    case+ tok.token_node of TOKsingleton c => c0 = c | _ => false
  )

val LPAREN = litchar '\('
val RPAREN = litchar ')'
val LBRACKET = litchar '\['
val RBRACKET = litchar ']'
val LBRACE = litchar '\{'
val RBRACE = litchar '}'

val COMMA = litchar ','
val SEMICOLON = litchar ';'

(* ****** ****** *)

fn litident (name0: string): P token =
  anytoken \sat (lam (tok: token): bool =<cloref>
    case+ tok.token_node of TOKide name => name0 = name | _ => false
  )
// end of [litident]

//

val COLON = litident ":"
val DOT = litident "."

val UMINUS = litident "~"

val PLUS = litident "+"
val MINUS = litident "-"
val TIMES = litident "*"
val DIVIDE = litident "/"

val EQ = litident "="
val NEQ = litident "<>"
val COLONEQ = litident ":="

val GTEQ = litident ">="
val GT = litident ">"
val LTEQ = litident "<="
val LT = litident "<"

val AMP = litident "&"
val BAR = litident "|"

//

val MINUSGT = litident "->"

//

val AND = litident"and"
val APP = litident"app"
val ELSE = litident"else"
val END = litident"end"
val FALSE = litident"false"
val FI = litident"fi"
val FN = litident"fn"
val FUN = litident"fun"
val IF = litident"if"
val IN = litident"in"
val LAM = litident"lam"
val LET = litident"let"
val PRINT = litident"print"
val THEN = litident"then"
val TRUE = litident"true"

(* ****** ****** *)

local

val arrsz = $arrsz {string} (
  "and"
, "else"
, "end"
, "fun"
, "if"
, "in"
, "lam"
, "let"
, "then"
, "|", "&"
, ".", ":"
, "+", "-", "/", "*"
, "=",":="
, ">=", ">", "<=", "<", "<>"
) // end of [arrsz]

in // in of [local]

val theKeywordArrSz = arrsz.3
val theKeywordArray = array_make_arraysize {string} arrsz

end // end of [local]

(* ****** ****** *)

fn isKeyword
  (name0: string):<> bool = ans where {
  var i: Nat = 0 and ans: bool = false
  val () = $effmask_all (
    while (i < theKeywordArrSz) let
      val name = theKeywordArray[i] in
      if name0 = name then (ans := true; break); i := i+1
    end // end of [while]
  ) // end of [val]
} (* end of [isKeyword] *)

(* ****** ****** *)

val p_ident: P token =
  anytoken \sat (lam (tok: token): bool =<fun> case+ tok.token_node of
    | TOKide name => if isKeyword name then false else true | _ => false
  )
// end of [p_ident]

val p_number: P token =
  anytoken \sat (lam (tok: token): bool =<fun>
    case+ tok.token_node of TOKint _ => true | _ => false
  )
// end of [p_number]

val p_string: P token =
  anytoken \sat (lam (tok: token): bool =<fun>
    case+ tok.token_node of TOKstr _ => true | _ => false
  )
// end of [p_string]

(* ****** ****** *)

local

#define PLUS_precedence 40
#define MINUS_precedence 40

#define TIMES_precedence 60
#define DIVIDE_precedence 60

#define UMINUS_precedence 80

#define EQ_precedence 20
#define NEQ_precedence 20

#define GTEQ_precedence 20
#define GT_precedence 20
#define LTEQ_precedence 20
#define LT_precedence 20

#define AMP_precedence 9
#define BAR_precedence 8

#define L LeftAssoc; #define R RightAssoc; #define N NonAssoc

in // in of [local]

val p_opr: P (fixopr e0xp) = begin
  PLUS wth (
    lam (tok: token) =<fun> f_infix (tok, L, PLUS_precedence, OPRplus)
  ) ||
  MINUS wth (
    lam (tok: token) =<fun> f_infix (tok, L, MINUS_precedence, OPRminus)
  ) ||
  TIMES wth (
    lam (tok: token) =<fun> f_infix (tok, L, TIMES_precedence, OPRtimes)
  ) ||
  DIVIDE wth (
    lam (tok: token) =<fun> f_infix (tok, L, DIVIDE_precedence, OPRslash)
  ) ||
  GTEQ wth (
    lam (tok: token) =<fun> f_infix (tok, N, GTEQ_precedence, OPRgte)
  ) ||
  GT wth (
    lam (tok: token) =<fun> f_infix (tok, N, GT_precedence, OPRgt)
  ) ||
  LTEQ wth (
    lam (tok: token) =<fun> f_infix (tok, N, LTEQ_precedence, OPRlte)
  ) ||
  LT wth (
    lam (tok: token) =<fun> f_infix (tok, N, LT_precedence, OPRlte)
  ) ||
  EQ wth (
    lam (tok: token) =<fun> f_infix (tok, N, EQ_precedence, OPReq)
  ) ||
  NEQ wth (
    lam (tok: token) =<fun> f_infix (tok, N, NEQ_precedence, OPRneq)
  ) ||
  UMINUS wth (
    lam (tok: token) =<fun> f_prefx (tok, UMINUS_precedence, OPRuminus)
  )
end where {
  fn f_prefx
    (tok: token, prec: int, opr: opr)
    :<> fixopr e0xp = let
    val tok_loc = tok.token_loc
    val f = lam (e: e0xp): e0xp =<cloref> let
      val loc = location_combine (tok_loc, e.e0xp_loc)
    in
      e0xp_make_opr (loc, opr, '[e])
    end // end of [f]
  in
    Prefix (tok.token_loc, prec, f)
  end // end of [f_minus]
  fn f_infix
    (tok: token, assoc: assoc, prec: int, opr: opr)
    :<> fixopr e0xp = let
    val f = lam
      (e1: e0xp, e2: e0xp): e0xp =<cloref> let
      val loc = location_combine (e1.e0xp_loc, e2.e0xp_loc) in
      e0xp_make_opr (loc, opr, '[e1, e2])
    end // end of [f]
  in
    Infix (tok.token_loc, prec, assoc, f)
  end // end of [f_infix]
} (* end of [where] *)

end // end of [local]
  
(* ****** ****** *)

fn symbol_make_token
  (tok: token):<> sym = let
  val- TOKide name = tok.token_node
in
  $effmask_all (symbol_make_name name)
end // end of [symbol_make_token]

(* ****** ****** *)

(*
** ty0 = sym | (ty, ..., ty); ty = ty0 | ty0 -> ty
*)

typedef typc = typ -<cloref> typ

val
rec lp_typ: LP (typ) = $delay (
  seq2wth_parser_fun (lzeta lp_typ1, lzeta lp_typc, f)
) where {
  val f = lam (t: typ, tc: typc) =<fun> tc (t) 
} (* end of [lp_typ] *)

and lp_typlist: LP typlst = $delay (
  repeat0_sep_parser<typ,token> (!lp_typ, COMMA)
) // end of [lp_typlst]

and lp_typ1: LP (typ) = $delay (
  p_ident wth f_ident ||
  seq3wth_parser_fun (LPAREN, lzeta lp_typlist, RPAREN, f_seq)
) where {
  val f_ident = lam
    (tk_id: token) =<> let
    val loc = tk_id.token_loc; val sym_id = symbol_make_token tk_id
  in
    typ_make_sym (loc, sym_id)
  end // end of [f_ident]
  val f_seq = lam
    (tk1: token, ts: typlst, tk2: token) =<> let
    val loc = location_combine (tk1.token_loc, tk2.token_loc) in
    typ_make_list (loc, ts)
  end // end of [f_seq]  
} (* end of [lp_typ1] *)

and lp_typc: LP (typc) = $delay (
  seq2wth_parser_fun (MINUSGT, !lp_typ, f)
) where {
  val f = lam
    (_: token, t_res: typ): typc =<fun> (lam t_arg => let
    val loc = location_combine (t_arg.typ_loc, t_res.typ_loc)
    val ts_arg = (case+ t_arg.typ_node of
      | TYPlist (ts_arg) => ts_arg | _ => list_cons (t_arg, list_nil)
    ) : typlst // end of [val]  
  in
    typ_make_fun (loc, ts_arg, t_res)
  end) // end of [val]
} (* end of [lp_typc] *)

(* ****** ****** *)

val lp_typann: LP (typopt) = $delay (
  seq2wth_parser_fun (COLON, !lp_typ, f_some) ||
  return_parser (None ())
) where {
  val f_some = lam (_: token, t: typ) =<fun> Some (t)
} // end of [lp_annty]

(* ****** ****** *)

val
rec lp_e0xp
  : LP (e0xp) = $delay (
  lzeta lp_e0xp_if ||
  lzeta lp_e0xp1
) // end of [lp_e0xp]

and lp_e0xplist: LP e0xplst = $delay (
  repeat0_sep_parser<e0xp,token> (!lp_e0xp, COMMA)
) // end of [p_explst]

(* ****** ****** *)

and lp_e0xp_if: LP e0xp = $delay (seq4wth_parser_fun
  (IF, !lp_e0xp, THEN >> !lp_e0xp, (ELSE >> !lp_e0xp)^?, f_if)
) where {
  fn f_if
    (tk_if: token, e1: e0xp, e2: e0xp, oe3: e0xpopt):<> e0xp = let
    val loc = case+ oe3 of
    | Some e3 => location_combine (tk_if.token_loc, e3.e0xp_loc)
    | None () => location_combine (tk_if.token_loc, e2.e0xp_loc)
  in
    e0xp_make_if (loc, e1, e2, oe3)
  end // end of [f_if]
} // end of [lp_e0xp_if]

(* ****** ****** *)
  
and lp_e0xp0: LP e0xp = $delay ( // ordering is significant!
  TRUE wth f_true ||
  FALSE wth f_false ||
  p_ident wth f_var ||
  p_number wth f_number ||
  p_string wth f_string ||
  seq3wth_parser_fun (LPAREN, !lp_e0xplist, RPAREN, f_list)
) where {
  fn f_var (tok: token):<> e0xp = let
    val loc = tok.token_loc; val sym = symbol_make_token tok in
    e0xp_make_var (loc, sym)
  end // end of [f_string]
  fn f_true (tok: token):<> e0xp = e0xp_make_bool (tok.token_loc, true)
  fn f_false (tok: token):<> e0xp = e0xp_make_bool (tok.token_loc, false)
  fn f_number (tok: token):<> e0xp = let
    val loc = tok.token_loc; val- TOKint int = tok.token_node in
    e0xp_make_int (loc, int)
  end // end of [f_string]
  fn f_string (tok: token):<> e0xp = let
    val loc = tok.token_loc; val- TOKstr str = tok.token_node in
    e0xp_make_str (loc, str)
  end // end of [f_string]
  fn f_list
    (tk_beg: token, es: e0xplst, tk_end: token):<> e0xp = begin
    case+ es of
    | list_cons (e, list_nil ()) => e | _ => let
        val loc = location_combine (tk_beg.token_loc, tk_end.token_loc)
      in
        e0xp_make_list (loc, es)
      end // end of [_]
  end // end of [f_seq]
} // end of [lp_e0xp0]

(* ****** ****** *)

and lp_opre0xp0: LP (fixitm e0xp) = $delay (
  p_opr wth f_opr || !lp_e0xp0 wth f_e0xp
) where {
  fn f_opr (opr: fixopr e0xp):<> fixitm e0xp =
    FIXITMopr opr
  fn f_e0xp (exp: e0xp):<> fixitm e0xp = FIXITMatm exp
} // end of [lp_opre0xp0]

(* ****** ****** *)

and lp_e0xp1: LP (e0xp) = $delay (
  (repeat1_parser !lp_opre0xp0) wth f
) where {
  typedef T = fixitm e0xp
  fn err (loc: loc): e0xp = begin
    prerr_location loc;
    prerr ": exit(STFPL)";
    prerr ": parsing failure: unresolved fixity";
    prerr_newline ();
    abort {e0xp} (1)
  end // end [err]

  fn fixitm_loc_get
    (itm: fixitm e0xp):<> loc = case+ itm of
    | FIXITMatm exp => exp.e0xp_loc
    | FIXITMopr opr => fixopr_loc_get opr
  // end of [fixitm_loc_get]

  fn f (itms: List1 T):<> e0xp = let
    val res = $effmask_all (fixity_resolve itms)
  in
    case+ res of
    | ~Some_vt e => e | ~None_vt () => let
        val+ list_cons (itm0, itms) = itms
        val loc0 = fixitm_loc_get (itm0)
        val loc01 = case+ itms of
          | list_cons _ => let
              val itm1 = list_last<T> (itms)
              val loc1 = fixitm_loc_get itm1
            in
              location_combine (loc0, loc1)
            end // end of [list_cons]
          | list_nil () => loc0
        // end of [val]
      in
        $effmask_all (err loc01) // report the error right here!
      end // end of [None_vt]
  end // end of [f]
} // end of [lp_e0xp1]

(* ****** ****** *)

extern fun parse_failure
  (tks: stream token, ncur: int, nmax: int): void

implement parse_failure (tks, ncur, nmax) = let
  fun loop
    (tks: stream token, n: int): Option_vt (token) =
    case+ !tks of
    | stream_cons (tk, tks) =>
        if n > 0 then loop (tks, n-1) else Some_vt (tk)
    | stream_nil () => None_vt ()
  // end of [loop]
  val otk = loop (tks, nmax - ncur)
in
  case+ otk of
  | ~Some_vt tk => begin
      prerr_location tk.token_loc;
      prerr ": exit(STFPL)";
      prerr ": parsing failure";
      prerr_newline ()
    end // end of [Some_vt]
  | ~None_vt () => begin
      prerr ": exit(STFPL)";
      prerr ": parsing failure at the end of the token stream.";
      prerr_newline ()
    end // end of [None_vt]
end // end of [parse_failure]

(* ****** ****** *)

fn parse_from_charstream (cs: stream char): e0xp = let
  val tks0 = tokenstream_make_charstream (cs)
  var tks: stream token = tks0
  var ncur: int = 0 and nmax: int = 0
  val r = apply_parser (!lp_e0xp, tks, ncur, nmax)
  val res = (case+ r of
    | ~Some_vt e => e
    | ~None_vt _ => let
        val () = parse_failure (tks, ncur, nmax) in abort {e0xp} (1)
      end // end of [Fail]
  ) : e0xp // end of [val]
  val otk = stream_item_get<token> (tks)
  val () = (case+ otk of
    | ~Some_vt tk => begin
        prerr_location tk.token_loc;
        prerr ": exit(STFPL)";
        prerr ": parsing failure: unconsumed token";
        prerr_newline ();
        abort {void} (1)
      end // end of [Some]
    // there are no unconsumed tokens
    | ~None_vt () => ()
  ) : void // end of [token]
in
  res
end // end of [parse_from_charstream]

(* ****** ****** *)

implement parse_from_stdin () = let
  val () = filename_push (filename_stdin)
  val cs = char_stream_make_file stdin_ref
  val res = parse_from_charstream (cs)
  val () = filename_pop ()
in
  res
end // end of [parse_from_stdin]

implement parse_from_file (filename) = let
  val fileref = open_file (filename, file_mode_r)
  val () = filename_push (filename) where
    { val filename = filename_make_string (filename) }
  // end of [val]
  val cs = char_stream_make_file fileref
  val res: e0xp = parse_from_charstream (cs)
  val () = filename_pop ()
  // ALERT: this should not be called as [fileref] may
  // val () = close_file (fileref) // have already been closed!!!
in
  res
end // end of [parse_from_file]

(* ****** ****** *)

(* end of [parser.dats] *)

////

infixl 4 << >>
infixl 3 &&
infixl 2 -- ##
infixl 2 wth suchthat return guard
infixr 1 ||

//

staload Char = "char.sats"
staload "io.sats"
staload List = "List/list.sats"
staload "option.sats"
staload String = "string.sats"

//

staload Error = "utils/ParsingCombinators/error.sats"
staload Input = "utils/ParsingCombinators/input.sats"

staload Pos = "utils/ParsingCombinators/pos.sats"
typedef Pos = $Pos.T

staload Token = "utils/ParsingCombinators/token.sats"
typedef Token = $Token.T

//

staload "utils/ParsingCombinators/parsing.sats"
typedef Parser (a:type, t:type) = T (a, t)

//

staload "parser.sats"

//

exception Fatal

fun fatal {a:type} (): a = raise Fatal

val keywords =
  '["abs", "and", "app", "else", "end", "false", "fi",
    "fn", "fun", "if", "in", "is", "let", "then", "true"]

val ABS = $Token.litWord "abs"
val UMINUS = $Token.litWord "~"
val PLUS = $Token.litWord "+"
val MINUS = $Token.litWord "-"
val STAR = $Token.litWord "*"
val SLASH = $Token.litWord "/"
val PERCENT = $Token.litWord "%"
val EQ = $Token.litWord "="
val EQEQ = $Token.litWord "=="
val EQGT = $Token.litWord "=>"
val NEQ = $Token.litWord "<>"
val LT = $Token.litWord "<"
val LTEQ = $Token.litWord "<="
val GT = $Token.litWord ">"
val GTEQ = $Token.litWord ">="
val COLON = $Token.litWord ":"
val COMMA = $Token.litWord ","
val UNDERSCORE = $Token.litWord "_"
val SEMICOLON = $Token.litWord ";"
val DOT = $Token.litWord "."
val SHARP = $Token.litWord "#"
val MINUSGT = $Token.litWord "->"

val LPAREN = $Token.litWord "("
val RPAREN = $Token.litWord ")"
val LBRACKET = $Token.litWord "["
val RBRACKET = $Token.litWord "]"
val LBRACE = $Token.litWord "{"
val RBRACE = $Token.litWord "}"

val QUOTE = $Token.litWord "'"

val AND = $Token.litWord "and"
val APP = $Token.litWord "app"
val ELSE = $Token.litWord "else"
val END = $Token.litWord "end"
val FALSE = $Token.litWord "false"
val FI = $Token.litWord "fi"
val FN = $Token.litWord "fn"
val FUN = $Token.litWord "fun"
val IF = $Token.litWord "if"
val IN = $Token.litWord "in"
val LET = $Token.litWord "let"
val PRINT = $Token.litWord "print"
val THEN = $Token.litWord "then"
val TRUE = $Token.litWord "true"

val BOOL = $Token.litWord "bool"
val INT = $Token.litWord "int"
val STRING = $Token.litWord "string"
val UNIT = $Token.litWord "unit"

fun ty2strList (ts: tys): String = $String.concatList ($List.map (ts, ty2str))

implement ty2str t =
  case t of
    | TYbase s => s
    | TYpair (t1, t2) => sprintf $fmt="TYtup (%s, %s)" (ty2str t1) (ty2str t2)
    | TYfun (ts, t) => sprintf $fmt="TYtup (%s, %s)" (ty2strList ts) (ty2str t)
    | TYlist ts => ty2strList ts
    | TYvar X => sprintf $fmt="TYvar(%d)" X.name
  
//

fun isLetter (c: Char): Bool =
  if $Char.isAlpha c then true else $Char.equal (c, '_')

fun isIdent (c: Char): Bool =
  if isLetter c then true
  else if $Char.isDigit c then true
  else $Char.equal (c, '\'')


(*
 * aty = bool | int | string | (typ)
 * ty = aty | aty -> typ | aty * ... * aty


fun aty (): Parser (ty, Token) =
  BOOL return (TYbase "bool") ||
  INT return (TYbase "int") ||
  STRING return (TYbase "string") ||
  UNIT return (TYbase "unit") ||
  LPAREN >> !ty << RPAREN

and ty (): Parser (ty, Token) =
  !aty && !ty' wth (lam '(t:ty, k:ty->ty): ty => k t) ||
  LPAREN >> !tys << RPAREN && !ty'' wth (lam '(ts:tys, k:tys->ty): ty => k ts)

and tys (): Parser (tys, Token) =
  !ty && repeat (COMMA >> !ty) wth (lam '(t:ty, ts: tys): tys => cons (t, ts)) ||
  succeed '[]

and ty' (): Parser (ty -> ty, Token) =
  MINUSGT >> !ty wth (lam (t:ty): ty->ty => lam (s:ty): ty => TYfun ('[s], t)) ||
  STAR >> !aty && !ty' wth (lam '(t:ty, k:ty->ty) => lam (s:ty): ty => k (TYpair (s, t))) ||
  succeed (lam (t:ty): ty => t)

and ty'' (): Parser (tys -> ty, Token) =
  MINUSGT >> !ty wth (lam (t:ty): tys->ty => lam (ts:tys): ty => TYfun (ts, t))

val oty: Parser (oty, Token) = COLON >> !ty wth some || succeed None

//

val int: Parser (Int, Token) = $Token.anyInteger

//

fun isKeyword (s: id): Bool =
  $List.exists {...} (keywords, lam x => $String.equal (x, s))

fun isVar (s: id): Bool =
  if isKeyword s then false
  else
    let
       val cs = $String.explode s
    in
       case cs of
	 | '[] => false
         | cons (c, cs) => if isLetter c then $List.forall (cs, isIdent) else false
    end

//

val var: Parser (id, Token) = $Token.anyWord suchthat isVar

//

fun exp0tostrList (es: exp0s): String =
  let
     fun aux (es: exp0s, res: List String): String =
       case es of
         | '[] => $String.concatList ($List.reverse res)
         | cons (e, es) =>
           aux (es, cons (exp0tostr e, cons (", ", res)))
  in
     case es of
       | '[] => ""
       | cons (e, es) => let val s = exp0tostr e in aux (es, '[s]) end
  end

implement exp0tostr (e: exp0): String =
  case e of
    | EXP0var x => sprintf $fmt="EXP0var(%s)" x
    | EXP0bool b => sprintf $fmt="EXP0bool(%b)" b
    | EXP0int i => sprintf $fmt="EXP0int(%i)" i
    | EXP0str s => sprintf $fmt="EXP0str(%s)" s
    | EXP0op (oper, es) => sprintf $fmt="EXP0op(%s; %s)" oper (exp0tostrList es)
    | EXP0tup es => sprintf $fmt="EXP0tup(%s)" (exp0tostrList es)
    | EXP0proj (e, n) => sprintf $fmt="EXP0proj(%s, %i)" (exp0tostr e) n
    | EXP0list es => sprintf $fmt="EXP0list(%s)" (exp0tostrList es)
    | EXP0if (e1, e2, e3) =>
      sprintf $fmt="EXP0if(%s, %s, %s)" (exp0tostr e1) (exp0tostr e2) (exp0tostr e3)
    | EXP0funs _ => "EXP0funs(...)"
    | EXP0choose (e, n) => sprintf $fmt="EXP0choose(%s, %i)" (exp0tostr e) n
    | EXP0app (e1, e2) => sprintf $fmt="EXP0app(%s, %s)" (exp0tostr e1) (exp0tostr e2)
    | EXP0let (x, e1, e2) =>
      sprintf $fmt="EXP0let(%s, %s, %s)" x (exp0tostr e1) (exp0tostr e2)
    | EXP0ann (e, t) => sprintf $fmt="EXP0ann(%s, %s)" (exp0tostr e) (ty2str t)

//

fun Abs (e: exp0): exp0 = EXP0op ("abs", '[e])
fun Neg (e: exp0): exp0 = EXP0op ("~", '[e])
fun Add (e1: exp0, e2: exp0): exp0 = EXP0op ("+", '[e1, e2])
fun Sub (e1: exp0, e2: exp0): exp0 = EXP0op ("-", '[e1, e2])
fun Mul (e1: exp0, e2: exp0): exp0 = EXP0op ("*", '[e1, e2])
fun Div (e1: exp0, e2: exp0): exp0 = EXP0op ("/", '[e1, e2])
fun Mod (e1: exp0, e2: exp0): exp0 = EXP0op ("%", '[e1, e2])
fun Gt (e1: exp0, e2: exp0): exp0 = EXP0op (">", '[e1, e2])
fun Gte (e1: exp0, e2: exp0): exp0 = EXP0op (">=", '[e1, e2])
fun Lt (e1: exp0, e2: exp0): exp0 = EXP0op ("<", '[e1, e2])
fun Lte (e1: exp0, e2: exp0): exp0 = EXP0op ("<=", '[e1, e2])
fun Eq (e1: exp0, e2: exp0): exp0 = EXP0op ("==", '[e1, e2])
fun Neq (e1: exp0, e2: exp0): exp0 = EXP0op ("<>", '[e1, e2])
fun Print (e: exp0): exp0 = EXP0op ("print", '[e])

//

(*
 * aexp = x | int | if exp then exp else exp fi
 *      | app (exp; exps) | let x = exp in exp end | (exps) 
 *
 * exp = aexp | aexp ... aexp | exp: typ
 * exps = exp, ..., exp
 *)

val opr: Parser (Fixity exp0, Token)  =
  ABS return Prefix(4, Abs) ||
  UMINUS return Prefix(4, Neg) ||
  PLUS return Infix(LeftAssoc, 2, Add) ||
  MINUS return Infix(LeftAssoc, 2, Sub) ||
  STAR return Infix(LeftAssoc, 3, Mul) ||
  SLASH return Infix(LeftAssoc, 3, Div) ||
  PERCENT return Infix(LeftAssoc, 3, Mod) ||
  GT return Infix(NonAssoc, 1, Gt) ||
  GTEQ return Infix(NonAssoc, 1, Gte) ||
  LT return Infix(NonAssoc, 1, Lt) ||
  LTEQ return Infix(NonAssoc, 1, Lte) ||
  EQEQ return Infix(NonAssoc, 1, Eq) ||
  NEQ return Infix(NonAssoc, 1, Neq) ||
  PRINT return Prefix (4, Print)

//

fun var_oty_list (): Parser (arg0s, Token) =
  (var && oty) && (repeat (COMMA >> var && oty))
  wth (lam '(xt: arg0, xts: arg0s): arg0s => cons (xt, xts)) ||
  succeed '[]

val proj: Parser (Int, Token) = DOT >> int

val choose: Parser (Int, Token) = SHARP >> int

val oFI: Parser (unit, Token) = FI return '() || succeed '()
val oEND: Parser (unit, Token) = END return '() || succeed '()

//

datatype modifier =
  | Empty
  | Proj of Int
  | Choose of Int

fun atExp (): Parser (exp0, Token) =
  var wth (lam (x: id) => EXP0var x) ||

  TRUE return (EXP0bool true) ||

  FALSE return (EXP0bool false) ||

  int wth (lam (i: Int): exp0 => EXP0int i) ||

  $Token.anyString wth (lam (s: String): exp0 => EXP0str s) ||

  IF >> !exp << THEN && !exp << ELSE && !exp << oFI wth
    (lam '( '(e1: exp0, e2: exp0), e3: exp0 ): exp0 => EXP0if (e1, e2, e3)) ||

  FN >> LPAREN >> !var_oty_list << RPAREN && oty && EQGT >> !exp wth
    (lam '( '(xts: arg0s, ot: oty), e: exp0 ): exp0 => EXP0funs '[ '("", xts, ot, e)]) ||

  FUN >> !fdef && (repeat (AND >> !fdef)) wth
    (lam '(fd: fdef0, fds: fdef0s ): exp0 => EXP0funs (cons (fd, fds))) ||

  LET >> var << EQ && !exp << IN && !exp << oEND wth
    (lam '( '(x: id, e1: exp0), e2: exp0 ) => EXP0let (x, e1, e2)) ||

  LPAREN >> !explist << RPAREN wth (lam (es: exp0s): exp0 => EXP0list es) ||

  QUOTE >> LPAREN >> !explist << RPAREN wth (lam (es: exp0s): exp0 => EXP0tup es)

and atsExp' (): Parser (modifier, Token) =
  proj wth (lam (n:Int): modifier => Proj n) ||
  choose wth (lam (n:Int): modifier => Choose n) ||
  succeed Empty

and exp0 (): Parser (exp0, Token) =
  !atExp && !atsExp' wth
     (lam '(e: exp0, m: modifier): exp0 =>
        case m of
          | Empty () => e
          | Proj n => EXP0proj (e, n)
          | Choose n => EXP0choose (e, n))

and exp1 (): Parser (exp0, Token) =
  !exp0 && !exp1' wth (lam '(e: exp0, k: exp0->exp0): exp0 => k e)

and exp1' (): Parser (exp0->exp0, Token) =
  !exp0  && !exp1' wth
    (lam '(e: exp0, k: exp0->exp0): exp0->exp0 => lam (e0: exp0): exp0 => k (EXP0app (e0, e))) ||

  succeed (lam (e: exp0): exp0 => e)

and opr_exp1 (): Parser (FixityItem exp0, Token) =
  opr wth (lam (p: Fixity exp0): FixityItem exp0 => Opr p) ||
  !exp1 wth (lam (e: exp0): FixityItem exp0 => Atm e)

and fdef (): Parser (fdef0, Token) =
  var && LPAREN >> !var_oty_list << RPAREN && oty && EQGT >> !exp wth
    (lam '( '( '(f: id, xts: arg0s), ot: oty ), e: exp0 ): fdef0 => '(f, xts, ot, e))

and exp2 (): Parser (exp0, Token) =
  repeat (!opr_exp1) wth
    (lam (items: List (FixityItem exp0)): exp0 => result (resolveFixity items))

and exp (): Parser (exp0, Token) =
  !exp2 && oty wth
    (lam '(e: exp0, ot: oty): exp0 =>
       case ot of None () => e | Some t => EXP0ann (e, t))

and explist (): Parser (exp0s, Token) =
  !exp && repeat (COMMA >> !exp) wth (lam '(e: exp0, es: exp0s): exp0s => cons (e, es)) ||
  succeed '[]

//

fun error {a:type} (msg: String) (pos: Pos): a =
  ($Error.error "parser" msg pos; raise Fatal)

//

implement parseKeybd () =
  let
     val '() = STDOUT # printLine "Please input an expression:"
     val s = $Input.readKeybd ()
     val s = $Pos.markStream s
     val ts = transform $Token.token s
     val p = op-- {exp0,exp0,Token} (!exp, done)
  in
     parseWith {exp0,exp0,Token}
       (lam x => x, lam pos => error ("Syntax error") pos, p, ts)
  end

implement parseFile (filename) =
  let
     val s = $Input.readFile (filename)
     val s = $Pos.markStream s
     val ts = transform $Token.token s
     val p = op-- {exp0,exp0,Token} (!exp, done)
  in
     parseWith {exp0,exp0,Token}
       (lam x => x, lam pos => error ("Syntax error") pos, p, ts)
  end

////
