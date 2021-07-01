
signature AST = sig

  datatype exp = Real of real
               | Let of string * exp * exp
               | Add of exp * exp
               | Sub of exp * exp
               | Mul of exp * exp
               | Var of string
               | App of string * exp
               | Tuple of exp list
               | Prj of int * exp

  type v
  val pp_v : v -> string
  val real_v : real -> v


  type env
  val init  : env
  val look   : env -> string -> v
  val insert : env -> string * v -> env
  val eval   : env -> exp -> v

  val parse  : {srcname:string,input:string} -> exp

  type prg = (string * string * exp) list

  val eval_prg : prg -> string -> v -> v
  val eval_exp : prg -> exp -> v
  val parse_prg : {srcname:string,input:string} -> prg
end

structure Ast :> AST = struct

fun debug_p () = false

structure T = SimpleToken

fun is_id s =
    size s > 0 andalso
    let val c0 = String.sub(s,0)
    in Char.isAlpha c0 orelse c0 = #"_"
    end andalso CharVector.all (fn c => Char.isAlphaNum c orelse c = #"_") s

fun string_to_real s : real option =
    let fun getC i =
            SOME(String.sub(s,i),i+1)
            handle _ => NONE
    in if CharVector.all (fn c => not(Char.isSpace c) andalso c <> #"~") s then
         case Real.scan getC 0 of
             SOME (r,i) => if i = size s then SOME r else NONE
           | NONE => NONE
       else NONE
    end

fun string_to_int s : int option =
    let fun getC i =
            SOME(String.sub(s,i),i+1)
            handle _ => NONE
    in if CharVector.all (fn c => not(Char.isSpace c) andalso c <> #"~") s then
         case Int.scan StringCvt.DEC getC 0 of
             SOME (n,i) => if i = size s then SOME n else NONE
           | NONE => NONE
       else NONE
    end

fun real_to_string r =
    CharVector.map (fn #"~" => #"-" | c => c) (Real.toString r)

fun is_num s =
    Option.isSome(string_to_real s)

fun tokens {srcname,input} =
    T.tokenise {sep_chars="(){}[],.;",
                symb_chars="#&|+-~^?*:!%/='<>@",
                is_id=is_id,
                is_num=is_num}
               {srcname=srcname,input=input}

fun prTokens ts =
    ( print "Tokens:\n"
    ; app (fn (t,r) => print (Region.pp r ^ ":" ^ T.pp_token t ^ ", ")) ts
    ; print "\n\n"
    )

fun lexing {srcname,input} =
    let val ts = tokens {srcname=srcname,input=input}
    in if debug_p() then prTokens ts else ()
     ; ts
    end

structure P = Parse(type token = T.token
                    val pp_token = T.pp_token)

open P

datatype exp = Real of real
             | Let of string * exp * exp
             | Add of exp * exp
             | Sub of exp * exp
             | Mul of exp * exp
             | Var of string
             | App of string * exp
             | Tuple of exp list
             | Prj of int * exp

datatype v = Real_v of real | Fun_v of v -> v | Tuple_v of v list

fun real_v r = Real_v r

type env = (string*v)list

fun pp_v (Real_v r) = real_to_string r
  | pp_v (Fun_v _) = "fn"
  | pp_v (Tuple_v vs) = "(" ^ String.concatWith "," (map pp_v vs) ^ ")"

fun lift1 s (opr : real -> real) : string * v =
    (s, Fun_v(fn (Real_v r) => Real_v(opr r)
               | _ => raise Fail ("eval: " ^ s ^ " expects a real argument")))

val init : env = [lift1 "abs" (fn r => if r < 0.0 then ~r else r),
                  lift1 "sin" Math.sin,
                  lift1 "cos" Math.cos,
                  lift1 "tan" Math.tan,
                  lift1 "exp" Math.exp,
                  lift1 "ln" Math.ln,
                  ("pi", Real_v (Math.pi))]

fun look nil x = raise Fail ("look: non-bound variable: " ^ x)
  | look ((k,v)::E) x = if k = x then v else look E x

fun insert (E:env) (k:string,v:v) : env = (k,v)::E

fun liftBin opr v1 v2 : v =
    case (v1,v2) of
        (Real_v r1, Real_v r2) => Real_v(opr(r1,r2))
      | _ =>  raise Fail "liftBin: expecting reals"

fun eval (E:env) (e:exp) : v =
    case e of
        Real r => Real_v r
      | Let(x,e1,e2) => eval ((x,eval E e1)::E) e2
      | Var x => look E x
      | Add(e1,e2) => liftBin op+ (eval E e1) (eval E e2)
      | Sub(e1,e2) => liftBin op- (eval E e1) (eval E e2)
      | Mul(e1,e2) => liftBin op* (eval E e1) (eval E e2)
      | App (f,e) => (case look E f of
                          Fun_v f => f (eval E e)
                        | _ => raise Fail ("eval(app): expecting function - " ^ f))
      | Tuple es => Tuple_v (map (eval E) es)
      | Prj(i,e) => (case eval E e of
                         Tuple_v vs => (List.nth (vs,i-1) handle _ => raise Fail "eval(prj): index (1-based) out of bound")
                       | _ => raise Fail "eval(prj): expecting tuple")

fun locOfTs nil = Region.botloc
  | locOfTs ((_,(l,_))::_) = l

val kws = ["let", "in", "end", "fun"]

val p_int : int p =
 fn ts =>
    case ts of
        (T.Num n,r)::ts' =>
        (case Int.fromString n of
             SOME n => OK (n,r,ts')
           | NONE => NO(locOfTs ts, fn () => "int"))
      | _ => NO(locOfTs ts, fn () => "int")

val p_real : real p =
 fn ts =>
    case ts of
        (T.Num n,r)::ts' =>
        (case Real.fromString n of
             SOME n => OK (n,r,ts')
           | NONE => NO(locOfTs ts, fn () => "real"))
      | _ => NO(locOfTs ts, fn () => "real")

val p_kw : string -> unit p =
 fn s => fn ts =>
    case ts of
        (T.Id k,r)::ts' =>
        if k = s then OK ((),r,ts')
        else NO(locOfTs ts, fn () => "expecting keyword '" ^ s ^ "', but found identifier '" ^ k ^ "'")
      | _ => NO(locOfTs ts, fn () => "expecting keyword '" ^ s ^ "', but found number or symbol")

val p_var : string p =
 fn ts =>
    case ts of
        (T.Id k,r)::ts' =>
        if not (List.exists (fn s => s = k) kws) then OK (k,r,ts')
        else NO(locOfTs ts, fn () => "expecting identifier, but found keyword '" ^ k ^ "'")
      | _ => NO(locOfTs ts, fn () => "expecting identifier, but found number or symbol")

val p_symb : string -> unit p =
 fn s => fn ts =>
    case ts of
        (T.Symb k,r)::ts' =>
        if k = s then OK ((),r,ts')
        else NO(locOfTs ts, fn () => "symb1")
      | (T.Id k,r)::_ => NO(locOfTs ts, fn () => ("symb: found id " ^ k))
      | _ => NO(locOfTs ts, fn () => "symb2")

infix >>> ->> >>- oo || ?? ??*

fun p_seq start finish (p: 'a p) : 'a list p =
    fn ts =>
       ((((((p_symb start ->> p) oo (fn x => [x])) ??* (p_symb "," ->> p)) (fn (xs,x) => x::xs)) >>- p_symb finish) oo List.rev)
           ts

val rec p_e : exp p =
    fn ts =>
       ( (p_e0 ??* ((p_bin "+" Add p_e0) || (p_bin "-" Sub p_e0))) (fn (e,f) => f e)
       ) ts

and p_e0 : exp p =
    fn ts =>
       ( (p_ae ??* p_bin "*" Mul p_ae) (fn (e,f) => f e)
       ) ts

and p_ae : exp p =
    fn ts =>
       (    ((p_var >>> p_ae) oo (fn(v,e) => App(v,e)))
         || (p_var oo Var)
         || (p_real oo Real)
         || (((p_symb "#" ->> p_int) >>> p_e) oo Prj)
         || ((p_seq "(" ")" p_e) oo (fn [e] => e | es => Tuple es))
         || (((p_kw "let" ->> p_var) >>> ((p_symb "=" ->> p_e) >>> (p_kw "in" ->> p_e)) >>- p_kw "end") oo (fn (v,(e1,e2)) => Let(v,e1,e2)))
       ) ts

and p_bin : string -> (exp*exp->exp) -> exp p -> (exp -> exp) p =
 fn opr => fn f => fn p =>
 fn ts =>
    ( (p_symb opr ->> p) oo (fn e2 => fn e1 => f(e1,e2))
    ) ts

fun parse0 (p: 'a p) {srcname,input} : 'a =
    let val ts = lexing {srcname=srcname,input=input}
    in case p ts of
           OK(e,r,ts') =>
           (case ts' of
                nil => e
              | _ => ( prTokens ts' ; raise Fail ("Syntax error at location " ^ Region.ppLoc (#2 r))))
         | NO(l,f) => raise Fail (Region.ppLoc l ^ ": " ^ f())
    end

fun parse arg = parse0 p_e arg

(* Programs *)
type prg = (string * string * exp) list

val rec p_prg : prg p =
    fn ts =>
       (  ((((((p_kw "fun" ->> p_var) >>> p_var) >>- p_symb "=") >>> p_e) oo (fn ((f,x),e) => [(f,x,e)])) ??* p_prg) (op @)
       ) ts

val parse_prg = parse0 p_prg

fun eval_prg (prg:prg) (f:string) (v:v) : v =
    let fun addFun ((f,x,e:exp),E:env) : env =
            insert E (f,Fun_v(fn v => eval (insert E (x,v)) e))
        val E = List.foldl addFun init prg
    in case look E f of
           Fun_v f => f v
         | _ => raise Fail ("eval_prg: expecting function " ^ f)
    end

fun eval_exp (prg:prg) (e:exp) : v =
    let fun addFun ((f,x,e:exp),E:env) : env =
            insert E (f,Fun_v(fn v => eval (insert E (x,v)) e))
        val E = List.foldl addFun init prg
    in eval E e
    end

end
