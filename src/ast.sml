
structure Ast :> AST = struct

fun debug_p () = false

fun dieLoc l s =
    raise Fail (Region.ppLoc l ^ ": " ^ s)

fun dieReg r s =
    raise Fail (Region.pp r ^ ": " ^ s)

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
    let val s = CharVector.map (fn #"~" => #"-" | c => c) (Real.toString r)
    in if size s >= 2
          andalso String.sub(s,size s - 1) = #"0"
          andalso String.sub(s,size s - 2) = #"."
       then String.extract (s,0,SOME(size s - 2))
       else s
    end

fun int_to_string n =
    CharVector.map (fn #"~" => #"-" | c => c) (Int.toString n)

fun is_num s =
    Option.isSome(string_to_real s) orelse
    (size s > 0 andalso String.sub(s,size s - 1) = #"." andalso
     Option.isSome(string_to_int(String.substring(s,0,size s -1))))

fun tokens {srcname,input} =
    T.tokenise {sep_chars="(){}[],;",
                symb_chars="#&|+-~^?*:!%/='<>@",
                is_id=is_id,
                is_num=is_num}
               {srcname=srcname,input=input}

fun prTokens ts =
    ( print ("Tokens:\n")
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

datatype 'i exp = Real of real * 'i
                | Int of int * 'i
                | Zero of 'i
                | Let of string * 'i exp * 'i exp * 'i
                | Add of 'i exp * 'i exp * 'i
                | Sub of 'i exp * 'i exp * 'i
                | Mul of 'i exp * 'i exp * 'i
                | Smul of 'i exp * 'i exp * 'i
                | Var of string * 'i
                | App of string * 'i exp * 'i
                | Tuple of 'i exp list * 'i
                | Prj of int * 'i exp * 'i
                | Map of string * 'i exp * 'i exp * 'i
                | Iota of int * 'i
                | Pow of real * 'i exp * 'i
                | Red of 'i rel * 'i exp * 'i
                | Array of 'i exp list * 'i
                | Range of 'i exp * 'i exp * 'i exp * 'i
       and 'i rel = Func of string * ('i exp) option * 'i exp * 'i exp * 'i
                | Trans of 'i rel * 'i
                | Comp of 'i rel * 'i rel * 'i
                | Pairs of 'i exp * 'i

fun par p x s =
    if x > p then s else "(" ^ s ^ ")"

fun pr_exp (e: 'i exp) : string =
    let fun pr (p:int) (e: 'i exp) : string =
            case e of
                Real (r,_) =>
                let val s = real_to_string r
                in if p = 9 then " " ^ s else s
                end
              | Int (n,_) =>
                 let val s = int_to_string n
                 in if p = 9 then " " ^ s else s
                 end
              | Zero r =>  if p = 9 then " 0" else "0"
              | Let (x,e1,e2,_) => "let " ^ x ^ " = " ^ pr 0 e1 ^ " in " ^ pr 0 e2 ^ " end"
              | Add (e1,e2,_) => par p 6 (pr 6 e1 ^ "+" ^ pr 6 e2)
              | Sub (e1,e2,_) => par p 6 (pr 6 e1 ^ "-" ^ pr 6 e2)
              | Mul (e1,e2,_) => par p 7 (pr 7 e1 ^ "*" ^ pr 7 e2)
              | Smul (e1,e2,_) => par p 7 (pr 7 e1 ^ "*>" ^ pr 7 e2)
              | Var (x,_) => if p = 9 then " " ^ x else x
              | App (f,e,_) => par p 8 (f ^ pr 9 e)
              | Tuple (es,_) => "(" ^ String.concatWith "," (map (pr 0) es) ^ ")"
              | Prj (i,e,_) => "#" ^ Int.toString i ^ " " ^ par p 8 (pr 8 e)
              | Map (x,f,es,_) => "map (fn " ^ x ^ " => " ^ pr 0 f ^ ") " ^ "(" ^ pr 0 es ^ ")"
              | Iota (n,_)  => "iota " ^ Int.toString n
              | Pow (r,e,_) => "pow " ^ real_to_string r ^ " " ^ par p 8 (pr 8 e)
              | Red (r, es, _) => "red (" ^ pr_rel r ^ ") (" ^ pr 0 es ^ ")"
              | Array (es, _) => "[" ^ String.concatWith "," (map (pr 0) es) ^ "]"
              | Range (from,to,step,_) => "[" ^ pr 0 from ^ ".." ^ pr 0 to ^ "," ^ pr 0 step ^ "]"
    in pr 0 e
    end
and pr_rel (r: 'i rel) : string =
    case r of
      Func (f,arg,from,to,_) =>
        f ^
        (case arg of
          SOME e => " " ^ pr_exp e ^ " "
        | NONE => ""
        ) ^ pr_exp from ^ " " ^ pr_exp to
      | Trans (r, _) => "(" ^ pr_rel r ^ ")!"
      | Comp (r1, r2,_)  => pr_rel r1 ^ " o " ^ pr_rel r2
      | Pairs (es, _) => pr_exp es

datatype v = Real_v of real
           | Int_v of int
           | Fun_v of v -> v
           | Tuple_v of v list
           | Array_v of v list
           | Zero_v

fun real_v r = Real_v r

type 'a env = (string * 'a)list

fun pr_v (Real_v r) = real_to_string r
  | pr_v (Int_v n) = int_to_string n
  | pr_v Zero_v = "0"
  | pr_v (Fun_v _) = "fn"
  | pr_v (Tuple_v vs) = "(" ^ String.concatWith "," (map pr_v vs) ^ ")"
  | pr_v (Array_v vs) = "[" ^ String.concatWith "," (map pr_v vs) ^ "]"

fun toReal s (v:v) : real =
    case v of
        Real_v r => r
      | Zero_v => 0.0
      | _ => raise Fail ("eval: " ^ s ^ " expecting real")

fun lift1r s (opr : real -> real) : string * v =
    (s, Fun_v(fn v => Real_v(opr (toReal s v))))

fun lift_rxr_r s (opr : real * real -> real) : string * v =
    (s, Fun_v(fn (Tuple_v[v1,v2]) =>
                 let val r1 = toReal s v1
                     val r2 = toReal s v2
                     val r' = opr (r1,r2)
                 in Real_v r'
                 end
               | Zero_v => Zero_v  (* works for norm2sq *)
               | _ => raise Fail ("eval: " ^ s ^ " expects a pair of reals as argument")))

fun lift_rNxrN_r s (opr : real list * real list -> real) : string * v =
    (s, Fun_v(fn (Tuple_v[Array_v vs1,Array_v vs2]) =>
                 let val rs1 = map (toReal s) vs1
                     val rs2 = map (toReal s) vs2
                 in Real_v(opr (rs1,rs2))
                 end
               | _ => raise Fail ("eval: " ^ s ^ " expects a pair of real arrays as argument")))

fun lift_rxrN_rN s (opr : real * real list -> real list) : string * v =
    (s, Fun_v(fn (Tuple_v[v,Array_v vs]) =>
                 let val r = toReal s v
                     val rs = map (toReal s) vs
                     val rs' = opr (r,rs)
                     val vs' = map Real_v rs'
                 in Array_v vs'
                 end
               | _ => raise Fail ("eval: " ^ s ^ " expects a pair of real and a real array as argument")))

fun lift_r3xr3_r3 s (opr : (real*real*real) * (real*real*real) -> (real*real*real)) : string * v =
    (s, Fun_v(fn (Tuple_v[Tuple_v[a1,a2,a3],
                          Tuple_v[b1,b2,b3]]) =>
                 let val (a1,a2,a3) = (toReal s a1,toReal s a2,toReal s a3)
                     val (b1,b2,b3) = (toReal s b1,toReal s b2,toReal s b3)
                     val (r1,r2,r3) = opr ((a1,a2,a3),(b1,b2,b3))
                 in Tuple_v[Real_v r1,Real_v r2,Real_v r3]
                 end
               | _ => raise Fail ("eval: " ^ s ^ " expects a pair of two triples of reals")))

fun lift_r3xr3_r s (opr : (real*real*real) * (real*real*real) -> real) : string * v =
    (s, Fun_v(fn (Tuple_v[Tuple_v[a1,a2,a3],
                          Tuple_v[b1,b2,b3]]) =>
                 let val (a1,a2,a3) = (toReal s a1,toReal s a2,toReal s a3)
                     val (b1,b2,b3) = (toReal s b1,toReal s b2,toReal s b3)
                     val r' = opr ((a1,a2,a3),(b1,b2,b3))
                 in Real_v r'
                 end
               | Zero_v => Zero_v
               | _ => raise Fail ("eval: " ^ s ^ " expects a pair of two triples of reals")))

fun lift_rNxrN_rN s (opr : real list * real list -> real list) : string * v =
    (s, Fun_v(fn (Tuple_v[Array_v vs1,
                          Array_v vs2]) =>
                 let val rs1 = map (toReal s) vs1
                     val rs2 = map (toReal s) vs2
                     val rs = opr (rs1,rs2)
                 in Array_v (map Real_v rs)
                 end
               | _ => raise Fail ("eval: " ^ s ^ " expects a pair of two real arrays")))

val VEinit : v env =
    [lift1r "abs" (fn r => if r < 0.0 then ~r else r),
     lift1r "sin" Math.sin,
     lift1r "cos" Math.cos,
     lift1r "tan" Math.tan,
     lift1r "exp" Math.exp,
     lift1r "ln" Math.ln,
     lift_rNxrN_r "dprod" (ListPair.foldlEq(fn (r1,r2,a) => a + (r1*r2)) 0.0),
     lift_rxrN_rN "sprod" (fn (r,rs) => List.map (fn q => q*r) rs),
     lift_r3xr3_r3 "cprod3" (fn ((a1,a2,a3),(b1,b2,b3)) =>
                                (a2*b3-a3*b2, a3*b1-a1*b3, a1*b2-a2*b1)),
     lift_r3xr3_r "dprod3" (fn ((a1,a2,a3),(b1,b2,b3)) => (a1*b1+a2*b2+a3*b3)),
     lift_rNxrN_rN "cross" (fn ([a1,a2,a3],[b1,b2,b3]) =>
                               [a2*b3-a3*b2, a3*b1-a1*b3, a1*b2-a2*b1]
                           | _ => raise Fail ("eval: cross is defined only in the three dimensional space")),
     lift_rxr_r "norm2sq" (fn (r1,r2) => Math.sqrt(r1*r1+r2*r2)),
     ("pi", Real_v (Math.pi))]

val VEempty : v env = nil

fun look nil x = NONE
  | look ((k,v)::E) x = if k = x then SOME v else look E x

fun insert (E: 'a env) (k:string,v:'a) : 'a env = (k,v)::E

fun plus (E1, E2) = E2 @ E1

fun liftNeg i v : v =
    case v of
        Real_v r => Real_v(~r)
      | Int_v i => Int_v(~i)
      | Tuple_v vs => Tuple_v (List.map (liftNeg i) vs)
      | Array_v vs => Array_v (List.map (liftNeg i) vs)
      | Zero_v => Zero_v
      | _ => dieReg i "liftNeg: expecting structured real value"

fun liftSub i (v1,v2) : v =
    case (v1,v2) of
        (Real_v r1, Real_v r2) => Real_v(r1-r2)
      | (Real_v r1, Int_v i2) => Real_v(r1 - real i2)
      | (Int_v i1, Real_v r2) => Real_v(real i1 - r2)
      | (Int_v i1, Int_v i2) => Int_v(i1-i2)
      | (Tuple_v vs1, Tuple_v vs2) =>
        (Tuple_v (ListPair.mapEq (liftSub i) (vs1,vs2))
         handle ListPair.UnequalLengths =>
                dieReg i "liftSub: expecting tuples of equal lengths")
      | (Array_v vs1, Array_v vs2) =>
        (Array_v (ListPair.mapEq (liftSub i) (vs1,vs2))
         handle ListPair.UnequalLengths =>
                dieReg i "liftSub: expecting arrays of equal lengths")
      | (v1,Zero_v) => v1
      | (Zero_v,v2) => liftNeg i v2
      | _ => dieReg i "liftSub: expecting matching structured values"

fun liftAdd i (v1,v2) : v =
    case (v1,v2) of
        (Real_v r1, Real_v r2) => Real_v(r1+r2)
      | (Real_v r1, Int_v i2) => Real_v(r1 + real i2)
      | (Int_v i1, Real_v r2) => Real_v(real i1 + r2)
      | (Int_v i1, Int_v i2) => Int_v(i1+i2)
      | (Tuple_v vs1, Tuple_v vs2) =>
        (Tuple_v (ListPair.mapEq (liftAdd i) (vs1,vs2))
         handle ListPair.UnequalLengths =>
                dieReg i "liftAdd: expecting tuples of equal lengths")
      | (Array_v vs1, Array_v vs2) =>
        (Array_v (ListPair.mapEq (liftAdd i) (vs1,vs2))
         handle ListPair.UnequalLengths =>
                dieReg i "liftAdd: expecting arrays of equal lengths")
      | (Zero_v,v2) => v2
      | (v1,Zero_v) => v1
      | _ => dieReg i ("liftAdd: expecting matching structured values - got "
                       ^ pr_v v1 ^ " and " ^ pr_v v2)

fun liftMul i (v1,v2) : v =
    case (v1,v2) of
        (Real_v r1, Real_v r2) => Real_v(r1*r2)
      | (Real_v r1, Int_v i2) => Real_v(r1 * real i2)
      | (Int_v i1, Real_v r2) => Real_v(real i1 * r2)
      | (Int_v i1, Int_v i2) => Int_v(i1*i2)
      | (Tuple_v vs1, Tuple_v vs2) =>
        (Tuple_v (ListPair.mapEq (liftAdd i) (vs1,vs2))
         handle ListPair.UnequalLengths =>
                dieReg i "liftMul: expecting tuples of equal lengths")
      | (Array_v vs1, Array_v vs2) =>
        (Array_v (ListPair.mapEq (liftMul i) (vs1,vs2))
         handle ListPair.UnequalLengths =>
                dieReg i "liftMul: expecting arrays of equal lengths")
      | (Zero_v,v2) => v1
      | (v1,Zero_v) => v2
      | _ => dieReg i ("liftMul: expecting matching structured values - got "
                       ^ pr_v v1 ^ " and " ^ pr_v v2)

fun liftSmulPow i opr v : v =
    case v of
        Real_v r => Real_v (opr r)
      | Tuple_v vs => Tuple_v (map (liftSmulPow i opr) vs)
      | Array_v vs => Array_v (map (liftSmulPow i opr) vs)
      | Zero_v => Zero_v (* ok for mul and pow *)
      | _ => dieReg i ("liftSmulPow: expecting structured value of reals - got " ^ pr_v v)

fun eval (regof:'i -> Region.reg) (E:v env) (e:'i exp) : v =
    let fun ev E e =
            case e of
                Real (r,_) => Real_v r
              | Int (n,_)  => Int_v n
              | Zero r => Zero_v
              | Let (x,e1,e2,_) => ev ((x,ev E e1)::E) e2
              | Var (x,i) =>
                (case look E x of
                     SOME v => v
                   | NONE => dieReg (regof i) ("unknown variable: " ^ x))
              | Add (e1,e2,i) => liftAdd (regof i) (ev E e1, ev E e2)
              | Sub (e1,e2,i) => liftSub (regof i) (ev E e1, ev E e2)
              | Mul (e1,e2,i) => liftMul (regof i) (ev E e1, ev E e2)
              | Smul (e1,e2,i) =>
                (case ev E e1 of
                     Real_v r => liftSmulPow (regof i) (fn r' => r * r') (ev E e2)
                   | _ => dieReg (regof i) ("expecting real as left argument to *>"))
              | App (f,e,i) => (case look E f of
                                    SOME(Fun_v f) => f (ev E e)
                                  | SOME _ => dieReg (regof i) ("expecting function but found " ^ f)
                                  | NONE => dieReg (regof i) ("unknown function: " ^ f))
              | Tuple (es,_) => Tuple_v (map (ev E) es)
              | Prj (i,e,info) => (case ev E e of
                                       Tuple_v vs => (List.nth (vs,i-1)
                                                      handle _ =>
                                                             dieReg (regof info) ("index (1-based) out of bound"))
                                     | Zero_v => Zero_v
                                     | _ => dieReg (regof info) "expecting tuple")
              | Map (x,f,es,info) =>
                (case ev E es of
                     Array_v vs => Array_v (List.map (fn v => ev (insert E (x, v)) f) vs)
                   | Zero_v => Zero_v
                   | _  => dieReg (regof info) "expecting array"
                )
              | Iota (n,_) => Array_v (List.tabulate (n, real_v o Real.fromInt))
              | Pow (r,e,i) => liftSmulPow (regof i)
                                          (fn r' => Math.pow(r',r))
                                          (ev E e)
              | Red (_,_,i) => dieReg (regof i) "eval: red unsupported"
              | Array (es, _)  => Array_v (map (ev E) es)
              | Range (from,to,step, i)  =>
                  case (ev E from, ev E to, ev E step) of
                      (Int_v from, Int_v to, Int_v step) =>
                        let fun eval_range (from, to, step) =
                              if from < to
                              then from :: eval_range (from + step, to, step)
                              else nil
                        in Array_v (map Int_v (eval_range (from, to, step)))
                        end
                      | _ => dieReg (regof i) "eval: expecting integer args to range"
    in ev E e
    end

fun locOfTs nil = Region.botloc
  | locOfTs ((_,(l,_))::_) = l

val kws = ["let", "in", "end", "fun", "map", "iota", "fn", "pow", "red"]

val p_zero : unit p =
 fn ts =>
    case ts of
        (T.Num "0",r)::ts' => OK ((),r,ts')
      | _ => NO(locOfTs ts, fn () => "zero")

val p_int : int p =
 fn ts =>
    case ts of
        (T.Num n,r)::ts' =>
        (case (Int.fromString n, List.exists (fn c => c = #".") (String.explode n)) of
             (SOME n, false) => OK (n,r,ts')
           | _ => NO(locOfTs ts, fn () => "int"))
      | _ => NO(locOfTs ts, fn () => "int")

val p_real : real p =
 fn ts =>
    case ts of
        (T.Num n,r)::ts' =>
        (case (Real.fromString n, List.exists (fn c => c = #".") (String.explode n)) of
             (SOME n, true) => OK (n,r,ts')
           | _ => NO(locOfTs ts, fn () => "real"))
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

infix >>> ->> >>- oo oor || ?? ??*

fun p_seq start finish (p: 'a p) : 'a list p =
    fn ts =>
       ((((((p_symb start ->> p) oo (fn x => [x])) ??* (p_symb "," ->> p)) (fn (xs,x) => x::xs)) >>- p_symb finish) oo List.rev)
           ts

type rexp = Region.reg exp
type rrel = Region.reg rel

val rec p_e : rexp p =
    fn ts =>
       ( (p_e0 ??* ((p_bin "+" Add p_e0) || (p_bin "-" Sub p_e0))) (fn (e,f) => f e)
       ) ts

and p_e0 : rexp p =
    fn ts =>
       ( (p_ae ??* ((p_bin "*" Mul p_ae) || (p_bin "*>" Smul p_e0))) (fn (e,f) => f e)
       ) ts

and p_ae : rexp p =
    fn ts =>
       (    ((p_var >>> p_ae) oor (fn ((v,e),r) => App(v,e,r)))
         || (((p_kw "pow" ->> p_real) >>> p_ae) oor (fn ((f,e),r) => Pow(f,e,r)))
         || (p_var oor Var)
         || (p_zero oor (fn ((),i) => Zero i))
         || (p_int oor Int)
         || (p_real oor Real)
         || (((p_symb "#" ->> p_int) >>> p_ae) oor (fn ((i,e),r) => Prj(i,e,r)))
         || ((p_seq "(" ")" p_e) oor (fn ([e],_) => e | (es,r) => Tuple (es,r)))
         || (((p_kw "let" ->> p_var) >>> ((p_symb "=" ->> p_e) >>> (p_kw "in" ->> p_e)) >>- p_kw "end") oor (fn ((v,(e1,e2)),r) => Let(v,e1,e2,r)))
         || (((p_kw "map" ->> ((p_symb "("
                              ->> (((p_kw "fn" ->> p_var) >>- p_symb "=>") >>> p_e))
                              >>- p_symb ")")) >>> p_ae)
                              oor (fn (((x, f), e), r) => Map (x, f, e, r)))
         || ((p_kw "iota" ->> p_int) oor (fn (n, r) => Iota (n, r)))
         || (((p_kw "red" ->> p_rrel) >>> p_ae) oor (fn ((rel, es), r) => Red (rel, es, r)))
         || ((p_seq "[" "]" p_e) oor Array)
         || (((((((p_symb "[" ->> p_e) >>- p_symb "..") >>> p_e)
             >>- p_symb ",") >>> p_e) >>- p_symb "]")
            oor (fn (((from,to),step), r) => Range (from,to,step,r)))
      ) ts

and p_bin : string -> (rexp*rexp*Region.reg->rexp) -> rexp p -> (rexp -> rexp) p =
 fn opr => fn f => fn p =>
 fn ts =>
    ( (p_symb opr ->> p) oor (fn (e2,r) => fn e1 => f(e1,e2,r))
    ) ts

and p_arel : rrel p =
      fn ts => (
        let val p_f = (((p_var oo (fn v => (v, NONE))) ?? p_ae) (fn ((v, _), arg) => (v, SOME arg)))
        in    ((p_symb "("  ->>
              ((p_f >>> (p_ae >>> p_ae))
              >>- p_symb ")"))
              oor (fn (((f, arg),(from, to)), r) => Func (f, arg, from, to, r)))
           || (p_ae oor Pairs)
        end ) ts

and p_rrel : rrel p =
    fn ts => (
         (((p_arel >>- p_symb "^") >>- p_symb "T") oor Trans)
      || (((p_arel >>- p_symb "o") >>> p_arel) oor (fn ((rel1, rel2), r) => Comp (rel1, rel2,r)))
      || p_arel
    ) ts

fun parse0 (p: 'a p) {srcname,input} : 'a =
    let val ts = lexing {srcname=srcname,input=input}
    in case p ts of
           NO(l,f) => dieLoc l (f())
         | OK(e,r,ts') =>
           case ts' of
               nil => e
             | _ => ( prTokens ts
                    ; dieLoc (#2 r) "syntax error"
                    )
    end

fun parse arg = parse0 p_e arg

(* ------------- *)
(* Programs      *)
(* ------------- *)

type 'i prg = (string * string * 'i exp * 'i) list

type rprg = Region.reg prg

val rec p_prg : rprg p =
    fn ts =>
       (  ((((((p_kw "fun" ->> p_var) >>> p_var) >>- p_symb "=") >>> p_e) oor (fn (((f,x),e),r) => [(f,x,e,r)])) ??* p_prg) (op @)
       ) ts

fun pr_prg (p: 'i prg) : string =
  case p of
     nil => ""
   | ((f,x,e,_)::ps) => "fun " ^ f ^ " " ^ x ^ " = " ^ pr_exp e  ^ "\n" ^ pr_prg ps

val parse_prg = parse0 p_prg

fun eval_prg (regof:'i->Region.reg) (prg: 'i prg) (f:string) (v:v) : v =
    let fun addFun ((f,x,e,_),VE:v env) : v env =
            insert VE (f,Fun_v(fn v => eval regof (insert VE (x,v)) e))
        val E = List.foldl addFun VEinit prg
    in case look E f of
           SOME (Fun_v f) => f v
         | SOME _ => raise Fail ("eval_prg: expecting function " ^ f)
         | NONE => raise Fail ("eval_prg: unknown function " ^ f)
    end

fun eval_exp (regof:'i->Region.reg) (prg: 'i prg) (e: 'i exp) : v =
    let fun addFun ((f,x,e,_),VE:v env) : v env =
            insert VE (f,Fun_v(fn v => eval regof (insert VE (x,v)) e))
        val E = List.foldl addFun VEinit prg
    in eval regof E e
    end

(* -------------- *)
(* Type inference *)
(* -------------- *)

datatype tinfo = Real_ti
               | Int_ti
               | Tuple_ti of ty list
               | Fun_ti of ty * ty
               | Tvar_ti of int * constraint list
               | Array_ti of ty
               | Rel_ti of ty * ty
     and constraint =
         NonFunTy
       | NumTy
       | ElemTy of int * ty
       | BaseTy of tinfo          (* tinfo is Real_ti or Int_ti *)

withtype ty = tinfo URef.uref

val fresh_ty0 : constraint list -> ty =
 let val c = ref 0
 in fn cs =>
       ( c := !c + 1
       ; URef.uref(Tvar_ti (!c,cs))
       )
 end

fun fresh_ty () = fresh_ty0 nil

val real_ty : ty = URef.uref Real_ti

val int_ty : ty = URef.uref Int_ti

fun num_ty () : ty =
    fresh_ty0 [NumTy]

fun nonfun_ty () : ty =
    fresh_ty0 [NonFunTy]

fun tuple_ty (ts : ty list) : ty =
    URef.uref (Tuple_ti ts)

fun fun_ty (t1:ty, t2:ty) : ty =
    URef.uref (Fun_ti (t1,t2))

fun rel_ty (t1:ty, t2:ty) : ty =
    URef.uref (Rel_ti (t1,t2))

fun array_ty (ty:ty) : ty =
    URef.uref (Array_ti ty)

fun pair_ty (t1,t2) = tuple_ty[t1,t2]

(* The following deconstructors assume that
 * type variables have been resolved *)

fun un_tuple (ty:ty) : ty list option =
    case URef.!! ty of
        Tuple_ti tys => SOME tys
      | _ => NONE

fun un_array (ty:ty) : ty option =
    case URef.!! ty of
        Array_ti ty => SOME ty
      | _ => NONE

fun un_fun (ty:ty) : (ty*ty) option =
    case URef.!! ty of
        Fun_ti tys => SOME tys
      | _ => NONE

fun is_real (ty:ty) : bool =
    case URef.!! ty of
        Real_ti => true
      | _ => false

(* The initial type environment *)

val real3_ty = tuple_ty[real_ty,real_ty,real_ty]

val real_arr_ty = array_ty real_ty

val TEinit : ty env =
    [("abs", fun_ty(real_ty,real_ty)),
     ("sin", fun_ty(real_ty,real_ty)),
     ("cos", fun_ty(real_ty,real_ty)),
     ("tan", fun_ty(real_ty,real_ty)),
     ("exp", fun_ty(real_ty,real_ty)),
     ("ln", fun_ty(real_ty,real_ty)),
     ("cprod3", fun_ty(pair_ty(real3_ty,real3_ty),real3_ty)),
     ("cross", fun_ty(pair_ty(real_arr_ty,real_arr_ty),real_arr_ty)),  (* cprod3 on arrays *)
     ("dprod3", fun_ty(pair_ty(real3_ty,real3_ty),real_ty)),
     ("dprod", fun_ty(pair_ty(real_arr_ty,real_arr_ty),real_ty)),
     ("sprod", fun_ty(pair_ty(real_ty,real_arr_ty),real_arr_ty)),
     ("norm2sq", fun_ty(pair_ty(real_ty,real_ty),real_ty)),
     ("pi", real_ty),
     ("to", fun_ty(int_ty, int_ty))]

val TEempty : ty env = nil

fun eq_ty (t1,t2) : bool =
    URef.eq (t1,t2) orelse eq_ti (URef.!! t1, URef.!! t2)
and eq_ti (ti1,ti2) =
    case (ti1, ti2) of
        (Real_ti, Real_ti) => true
      | (Tuple_ti ts1, Tuple_ti ts2) => eq_tys (ts1,ts2)
      | (Fun_ti (t1,t2),Fun_ti(t1',t2')) =>
        eq_ty(t1,t1') andalso eq_ty(t2,t2')
      | (Array_ti t1, Array_ti t2) => eq_ty (t1, t2)
      | _ => false
and eq_tys (nil,nil) = true
  | eq_tys (t1::ts1,t2::ts2) = eq_ty(t1,t2) andalso eq_tys(ts1,ts2)
  | eq_tys _ = false

fun pr_ty ty = pr_ti(URef.!! ty)
and pr_ti ti =
    case ti of
        Real_ti => "real"
      | Int_ti  => "int"
      | Tuple_ti ts => "(" ^ String.concatWith " * " (map pr_ty ts) ^ ")"
      | Fun_ti(t1,t2) =>  "(" ^ pr_ty t1 ^ " -> " ^ pr_ty t2 ^ ")"
      | Rel_ti(t1,t2) =>  "(" ^ pr_ty t1 ^ " X " ^ pr_ty t2 ^ ")"
      | Tvar_ti (i,_) =>  "'a" ^ Int.toString i
      | Array_ti t => "[]" ^ pr_ty t

(* Unification *)

fun unify_ty (r:Region.reg) (t1,t2) : unit =
    URef.unify (fn (Real_ti,Real_ti) => Real_ti
                 | (Int_ti,Int_ti) => Int_ti
                 | (ti as Tuple_ti ts1, Tuple_ti ts2) =>
                   ( unify_tys r (ts1,ts2) ; ti )
                 | (ti as Fun_ti(t1,t2), Fun_ti(t1',t2')) =>
                   ( unify_ty r (t1,t1') ; unify_ty r (t2,t2') ; ti )
                 | (ti as Array_ti t1, Array_ti t2) => (unify_ty r (t1, t2); ti)
                 | (Tvar_ti (i1,cs1), Tvar_ti (i2,cs2)) => Tvar_ti (Int.min(i1,i2), cs1 @ cs2)
                 | (Tvar_ti (_,cs), ti) => ( List.app (chk_constraint r ti) cs ; ti )
                 | (ti, Tvar_ti (_,cs)) => ( List.app (chk_constraint r ti) cs ; ti )
                 | _ => dieReg r ("failed to unify " ^ pr_ty t1 ^ " with " ^ pr_ty t2)
               ) (t1,t2)

and unify_tys r (ts1,ts2) =
    let fun f (nil,nil) = ()
          | f (t1::ts1,t2::ts2) = (unify_ty r (t1,t2) ; f (ts1,ts2) )
          | f _ = dieReg r ("failed to unify tuple type " ^ pr_ti (Tuple_ti ts1) ^
                            " with tuple type " ^ pr_ti (Tuple_ti ts2) ^
                            " of a different length")
    in f (ts1,ts2)
    end

and unify_all r nil = ()
  | unify_all r (ty::tys) =
    let fun f nil = ()
          | f (ty'::tys) = (unify_ty r (ty, ty'); f tys)
    in f tys
    end

and chk_constraint (r:Region.reg) ti c =
    case (c,ti) of
        (NonFunTy, Fun_ti _) => dieReg r "expecting non-function"
      | (NonFunTy, Rel_ti _) => dieReg r "expecting non-relation"
      | (NonFunTy, Tuple_ti ts) => app (fn t => chk_constraint r (URef.!! t) c) ts
      | (NonFunTy, Array_ti t) => chk_constraint r (URef.!! t) c
      | (NonFunTy, Real_ti) => ()
      | (NonFunTy, Int_ti) => ()
      | (NonFunTy, Tvar_ti _) => ()
      | (BaseTy ti', Fun_ti _) => dieReg r ("expecting non-function with base type " ^ pr_ti ti')
      | (BaseTy ti', Rel_ti _) => dieReg r ("expecting non-relation with base type " ^ pr_ti ti')
      | (BaseTy _, Array_ti t) => chk_constraint r (URef.!! t) c
      | (BaseTy _, Tuple_ti ts) => app (fn t => chk_constraint r (URef.!! t) c) ts
      | (BaseTy Real_ti, Real_ti) => ()
      | (BaseTy Int_ti, Int_ti) => ()
      | (BaseTy ti', _) => dieReg r ("expecting structural type with base type " ^ pr_ti ti' ^
                                     " but found type " ^ pr_ti ti)
      | (ElemTy(i,t), Tuple_ti ts) =>
        let val t' = List.nth(ts,i-1)
                     handle _ =>
                            dieReg r ("tuple projection " ^ Int.toString i ^
                                      " out of bound: tuple contains only " ^
                                      Int.toString (length ts) ^ " elements")
        in unify_ty r (t,t')
        end
      | (ElemTy(i,ty), _) => dieReg r ("expecting tuple type but found " ^ pr_ti ti)
      | (NumTy, Real_ti) => ()
      | (NumTy, Int_ti) => ()
      | (NumTy, _) => dieReg r ("expecting numeric type but found type " ^ pr_ti ti)

fun info_of_exp (e: 'i exp) : 'i =
    case e of
        Real(_,i) => i
      | Int(_,i) => i
      | Zero i => i
      | Let(_,_,_,i) => i
      | Add(_,_,i) => i
      | Sub(_,_,i) => i
      | Mul(_,_,i) => i
      | Smul(_,_,i) => i
      | Var (_,i) => i
      | App(_,_,i) => i
      | Tuple (_,i) => i
      | Prj(_,_,i) => i
      | Map(_,_,_,i) => i
      | Iota(_,i)  => i
      | Pow(_,_,i) => i
      | Red(_,_,i) => i
      | Array(_, i) => i
      | Range(_,_,_,i) => i

fun tyinf_exp (TE: ty env) (e:Region.reg exp) : (Region.reg*ty) exp * ty =
    let fun tyinf_svbin opr (e1,e2,r) =
            let val (e1',ty1) = tyinf_exp TE e1
                val (e2',ty2) = tyinf_exp TE e2
            in unify_ty (info_of_exp e1) (ty1,real_ty)
             ; (opr (e1',e2',(r,ty2)), ty2)
            end
        fun tyinf_vbin opr (e1,e2,r) =
            let val (e1',ty1) = tyinf_exp TE e1
                val (e2',ty2) = tyinf_exp TE e2
            in unify_ty (info_of_exp e2) (ty1,ty2)
             ; (opr (e1',e2',(r,ty1)), ty1)
            end
    (* Several operators (and values) are generic:
        - Add : 'a * 'a -> 'a
        - Sub : 'a * 'a -> 'a
        - Mul : 'a * 'a -> 'a
        - 0 : 'a
        - Smul : real * 'a -> 'a
     *)
    in case e of
           Real (f,r) => (Real (f,(r,real_ty)), real_ty)
         | Int (n,r)  =>
           let val t = num_ty()
           in (Int (n, (r,t)), t)
           end
         | Zero r =>
           let val t = nonfun_ty()
           in (Zero (r,t), t)
           end
         | Let (x,e1,e2,r) =>
           let val (e1',ty1) = tyinf_exp TE e1
               val (e2',ty2) = tyinf_exp (insert TE (x,ty1)) e2
           in (Let (x,e1',e2',(r,ty2)), ty2)
           end
         | Add (e1,e2,r) => tyinf_vbin Add (e1,e2,r)
         | Sub (e1,e2,r) => tyinf_vbin Sub (e1,e2,r)
         | Mul (e1,e2,r) => tyinf_vbin Mul (e1,e2,r)
         | Smul (e1,e2,r) => tyinf_svbin Smul (e1,e2,r)
         | Var (x,r) => (case look TE x of
                             SOME ty => (Var(x,(r,ty)),ty)
                           | NONE => dieReg r ("unknown variable: " ^ x))
         | App (f,e1,r) =>
           let val (e1',ty1) = tyinf_exp TE e1
           in case look TE f of
                  SOME tf =>
                  let val ty2 = fresh_ty()
                  in unify_ty r (tf,fun_ty(ty1,ty2))
                   ; (App(f,e1',(r,ty2)), ty2)
                  end
                | NONE => dieReg r ("unknown function: " ^ f)
           end
         | Tuple (es,r) =>
           let val ets = List.map (tyinf_exp TE) es
               val t = tuple_ty (map #2 ets)
           in (Tuple (map #1 ets,(r,t)), t)
           end
         | Prj (i,e1,r) =>
           let val (e1',ty1) = tyinf_exp TE e1
               val t = fresh_ty() (* result *)
               val t' = fresh_ty0 [ElemTy(i,t)]
           in unify_ty r (ty1, t')
            ; (Prj(i,e1',(r,t)),t)
           end
         | Iota (n,r) =>
               (Iota(n, (r, array_ty real_ty)), array_ty real_ty)
         | Map (x,f,es,r) =>
           let val ty_x = fresh_ty()
               val (f', ty_f) = tyinf_exp (insert TEinit (x, ty_x)) f
               val (es', ty_es) = tyinf_exp TE es
           in unify_ty r (ty_es, array_ty ty_x)
            ; (Map (x, f', es', (r, array_ty ty_f)), array_ty ty_f)
           end
         | Pow (f,e1,r) =>
           let val (e1',ty1) = tyinf_exp TE e1
           in unify_ty r (ty1,real_ty)
            ; (Pow (f,e1',(r,real_ty)), real_ty)
           end
         | Red (rel,es,r) =>
           let val (es', ty_es) = tyinf_exp TE es
               val (rel', _) = tyinf_rel TE rel
               val ty_x = fresh_ty()
           in unify_ty r (ty_es, array_ty ty_x)
            ; (Red (rel', es', (r, ty_es)), ty_es)
           end
         | Array (es,r) =>
           let val (es', tys) = ListPair.unzip (map (tyinf_exp TE) es)
               val ty = fresh_ty()
           in unify_all r (ty::tys)
           ; (Array(es', (r,array_ty ty)), array_ty ty)
           end
         | Range (from,to,step,r) =>
            let val (from', ty_from') = tyinf_exp TE from
                val (to', ty_to') = tyinf_exp TE to
                val (step', ty_step') = tyinf_exp TE step
            in unify_all r [int_ty, ty_from', ty_to', ty_step']
             ; (Range (from', to', step', (r, array_ty int_ty)), array_ty int_ty)
            end
    end
and tyinf_rel (TE: ty env) (rel:Region.reg rel) : (Region.reg*ty) rel * ty =
    case rel of
        Func (f,arg,from,to,r) =>
            let val (from', ty_from') = tyinf_exp TE from
                val (to', ty_to') = tyinf_exp TE to
            in unify_ty r (ty_from', array_ty int_ty)
             ; unify_ty r (ty_to', array_ty int_ty)
             ; (case look TE f of
                  SOME tf => unify_ty r (tf,fun_ty(int_ty,int_ty))
                | NONE => dieReg r ("unknown function: " ^ f))
             ; (case arg of
                 SOME arg =>
                  let val (arg', ty_arg) = tyinf_exp TE arg
                  in unify_ty r (ty_arg, int_ty)
                   ; (Func (f, SOME arg', from', to', (r, rel_ty(int_ty, int_ty))), rel_ty(int_ty, int_ty))
                  end
                | NONE => (Func (f, NONE, from', to', (r, rel_ty(int_ty, int_ty))), rel_ty(int_ty, int_ty))
               )
            end
      | Trans (rel, r) =>
        let val (rel', ty) = tyinf_rel TE rel
            val to_ty = fresh_ty()
            val from_ty = fresh_ty()
        in unify_ty r (rel_ty(from_ty, to_ty), ty)
         ; (Trans(rel', (r, rel_ty(to_ty, from_ty))), rel_ty(to_ty, from_ty))
        end
      | Comp (rel1, rel2, r) =>
        let val (rel1', ty1) = tyinf_rel TE rel1
            val (rel2', ty2) = tyinf_rel TE rel2
            val to_ty1 = fresh_ty()
            val from_ty1 = fresh_ty()
            val to_ty2 = fresh_ty()
            val from_ty2 = fresh_ty()
        in unify_ty r (rel_ty(from_ty1, to_ty1), ty1)
         ; unify_ty r (rel_ty(from_ty2, to_ty2), ty2)
         ; (Comp(rel1', rel2', (r, rel_ty(from_ty1, to_ty2))), rel_ty(from_ty1, to_ty2))
        end
      | Pairs (es,r) =>
        let val (es', ty) = tyinf_exp TE es
        in unify_ty r (array_ty (tuple_ty [int_ty, int_ty]), ty)
        ; (Pairs (es', (r, ty)), ty)
        end

val reg0 = (Region.botloc,Region.botloc)

(* Resolve non-instantiated type variables by analysing the
 * type constraints; non-constrained type variables are instantiated
 * to type real. Projection constraints guide the number of elements
 * and the element types in each tuple type. Notice: Projections
 * project from tuples, not from arrays. *)

fun resolve_t t =
    case URef.!! t of
        Tvar_ti (_, cs) =>
        let
            val base : tinfo option =
              List.foldl (fn (c,opt) =>
                             case (c,opt) of
                                 (NonFunTy, _) => opt
                               | (NumTy, _) => opt
                               | (BaseTy ti, NONE) => SOME ti
                               | (BaseTy ti, SOME ti') =>
                                 if eq_ti (ti, ti') then opt
                                 else dieReg reg0 ("cannot resolve type constraints due to incompatible base types "
                                                   ^ pr_ti ti ^ " and " ^ pr_ti ti')
                               | (ElemTy(i,_), _) => opt) NONE cs
            val (base, base_ty) =
                case base of
                    SOME b => (b, URef.uref b)
                  | NONE => (Real_ti, real_ty)

            val m = List.foldl (fn (c,m) =>
                                   case c of
                                       NonFunTy => m
                                     | BaseTy _ => m
                                     | NumTy => m
                                     | ElemTy(i,_) => Int.max(i,m)) 0 cs
            fun look j cs =
                case cs of
                    nil => NONE
                  | NonFunTy :: cs => look j cs
                  | BaseTy _ :: cs => look j cs
                  | NumTy :: cs => look j cs
                  | ElemTy(i,t) :: cs => if j = i then SOME t
                                         else look j cs
        in if m = 0 then URef.::=(t, base)
           else
             let val m = Int.max(2,m) (* at least two elements *)
                 val ts = List.tabulate(m, fn i => case look (i+1) cs of
                                                       SOME t => t
                                                     | NONE => base_ty)
             in unify_ty reg0 (tuple_ty ts, t)
              ; app resolve_t ts
             end
        end
      | Real_ti => ()
      | Int_ti  => ()
      | Tuple_ti ts => List.app resolve_t ts
      | Fun_ti(t1,t2) => (resolve_t t1 ; resolve_t t2)
      | Rel_ti(t1,t2) => (resolve_t t1 ; resolve_t t2)
      | Array_ti t => resolve_t t

fun resolve_e (e : (Region.reg*ty) exp) : unit =
    let val (_,t) = info_of_exp e
    in resolve_t t
    end

fun resolve_ints e =
    case e of
        Real _ => e
      | Int (n,(r,t)) => if is_real t then Real (real n,(r,t)) else e
      | Zero _ => e
      | Let (x,e1,e2,i) => Let (x,resolve_ints e1,resolve_ints e2,i)
      | Add (e1,e2,i) => Add (resolve_ints e1,resolve_ints e2,i)
      | Sub (e1,e2,i) => Sub (resolve_ints e1,resolve_ints e2,i)
      | Mul (e1,e2,i) => Mul (resolve_ints e1,resolve_ints e2,i)
      | Smul (e1,e2,i) => Smul (resolve_ints e1,resolve_ints e2,i)
      | App (f,e,i) => App (f,resolve_ints e,i)
      | Tuple (es,i) => Tuple (map resolve_ints es,i)
      | Prj (i,e,info) => Prj (i,resolve_ints e,info)
      | Map (x,f,es,info) => Map (x,resolve_ints f,resolve_ints es,info)
      | Iota (n,i) => Iota (n,i)
      | Pow (r,e,i) => Pow (r,resolve_ints e,i)
      | Red (_,_,_) => e
      | Array (es,i) => Array (map resolve_ints es,i)
      | Range (from,to,step,i) => Range (resolve_ints from,resolve_ints to,resolve_ints step,i)
      | Var _ => e

and resolve_rel r =
    case r of
        Func (s,NONE,e1,e2,i) => Func (s,NONE,resolve_ints e1,resolve_ints e2,i)
      | Func (s,SOME e',e1,e2,i) => Func (s,SOME(resolve_ints e'),resolve_ints e1,resolve_ints e2,i)
      | Trans (r,i) => Trans (resolve_rel r,i)
      | Comp (r1,r2,i) => Comp (resolve_rel r1,resolve_rel r2,i)
      | Pairs (e,i) => Pairs (resolve_ints e,i)

(* General type inference function *)
fun tyinf_prg (prg: Region.reg prg) : (Region.reg*ty) prg * ty env =
    let fun tyinf TE ((f,x,e,r)::rest) (prg_acc,TEacc) =
            let val ty = nonfun_ty()
                val (e',ty') = tyinf_exp (insert TE (x,ty)) e
                val fty = fun_ty(ty,ty')
                val TE' = insert TE (f, fty)
                val TEacc' = insert TEacc (f, fty)
                val prg_acc' = (f,x,e',(r,fty)) :: prg_acc
            in tyinf TE' rest (prg_acc',TEacc')
            end
          | tyinf _ nil (prg_acc,TEacc) = (rev prg_acc,TEacc)
        val (prg',TE) = tyinf TEinit prg (nil,TEempty)
        val () = List.app (fn (_,_,e',(_,fty)) =>
                              ( resolve_e e'
                              ; resolve_t fty )
                          ) prg'
        val prg'' = map (fn (f,x,e,r) =>
                            (f,x,resolve_ints e,r)) prg'
    in (prg'',TE)
    end

val tyinf_exp : ty env -> Region.reg exp -> (Region.reg*ty) exp * ty =
 fn TE => fn e =>
    let val (e,t) = tyinf_exp TE e
    in resolve_e e
     ; resolve_t t
     ; (resolve_ints e,t)
    end

end
