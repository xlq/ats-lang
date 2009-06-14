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
 *)

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

implement parseString (s): exp0 =
  let
     val s = $Input.readString s
     val s = $Pos.markStream s
     val ts = transform $Token.token s
     val p = op-- {exp0,exp0,Token} (!exp, done)
 in
     parseWith {exp0,exp0,Token}
       (lam x => x, lam pos => error ("Syntax error") pos, p, ts)
  end

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
