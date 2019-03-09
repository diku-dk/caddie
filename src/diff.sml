(* Dynamically tagged version of combinatory differentiation interpretation (in SML)
 *
 * Todo:
 *  1) More examples
 *  2) Experiment with forward/reverse mode differences
 *
 * Questions:
 *  1) Can we somehow convert point-free notation to expressions with let-expressions?
 *)

fun die s = (print ("Error: " ^ s ^ "\n"); raise Fail s)

signature PRIM = sig
  datatype uprim = Sin | Cos | Ln | Exp | Pow of real | Neg
  val pp_uprim : uprim -> string

  datatype bilin = Mul     (* : R x R -2> R            multiplication *)
                 | Cprod3  (* : R3 x R3 -2> R3         cross product *)
                 | Dprod   (* : RN x RN -2> R          dot product *)
                 | Sprod   (* : R * RN -2> RN          scalar product *)
                 | Norm2Sq (* : R x R -2> R            \(x,y).(x^2+y^2) *)
  val pp_bilin : bilin -> string    (* all to be printed infix *)

  val mul      : real * real -> real
  val cprod3   : real list * real list -> real list
  val dprod    : real list * real list -> real
  val sprod    : real * real list -> real list
  val norm2sq  : real * real -> real

  val eq_bilin : bilin * bilin -> bool
  val eq_uprim : uprim * uprim -> bool
  val uprim : uprim -> real -> real
end

structure Prim :> PRIM = struct
  datatype uprim = Sin | Cos | Ln | Exp | Pow of real | Neg
  fun pp_uprim (p: uprim) : string =
      case p of
          Sin => "sin"
        | Cos => "cos"
        | Ln => "ln"
        | Exp => "exp"
        | Neg => "~"
        | Pow r => "pow(" ^ Real.toString r ^ ")"
  datatype bilin = Mul     (* : R x R -> R             multiplication *)
                 | Cprod3  (* : R3 x R3 -2> R3         cross product *)
                 | Dprod   (* : RN x RN -2> R          dot product *)
                 | Sprod   (* : R x RN -2> RN          scalar product *)
                 | Norm2Sq (* : R x R -> R             \(x,y).(x^2+y^2) *)
  fun pp_bilin b =
      case b of
          Mul => "*"    (* all to be printed infix *)
        | Cprod3 => "x"
        | Dprod => "dot"
        | Sprod => "."
        | Norm2Sq => "norm2sq"

  val mul : real * real -> real = op *
  fun cprod3 ([a1,a2,a3], [b1,b2,b3]) : real list =
    [a2*b3-a3*b2, a3*b1-a1*b3, a1*b2-a2*b1]
    | cprod3 _ = die "cprod3 expects two triples of reals"

  fun dprod (rs1, rs2) : real =
      let val ps = List.map mul (ListPair.zip (rs1,rs2))
      in List.foldl (fn (v,a) => v + a) 0.0 ps
      end handle _ => die "dprod expects equal length tuples"

  fun sprod (s,rs) = List.map (fn v => mul(s,v)) rs

  fun norm2sq (x,y) : real = x*x+y*y

  fun uprim p : real -> real =
      case p of
          Sin => Math.sin
        | Cos => Math.cos
        | Ln => Math.ln
        | Exp => Math.exp
        | Neg => Real.~
        | Pow r => (fn x => Math.pow(x,r))

  val eq_bilin : bilin * bilin -> bool = op =
  val eq_uprim : uprim * uprim -> bool =
   fn (Sin,Sin) => true
    | (Cos,Cos) => true
    | (Ln,Ln) => true
    | (Exp,Exp) =>  true
    | (Neg,Neg) => true
    | (Pow r,Pow r') => Real.==(r,r')
    | _ => false

end

signature VAL = sig
  type v
  val R   : real -> v
  val T   : v list -> v
  val VarOpt : (string -> v) option

  val unT : v -> v list option
  val unR : v -> real option
  val pp : v -> string
  val prjI : string -> int -> v -> v
  val add : v -> v
  val uprim : Prim.uprim -> v -> v
  val uprim_diff : Prim.uprim -> v -> v
  val bilin : Prim.bilin * v -> v

  val isComplex : v -> bool

  type 'a M
  val ret : 'a -> 'a M
  val >>= : 'a M * ('a -> 'b M) -> 'b M
  val letBind : v -> v M
  val ppM : string -> ('a -> string) -> 'a M -> string
  val getVal : 'a M -> 'a
  val eq : v * v -> bool
end

structure Val :> VAL = struct
datatype v = R of real | T of v list
val VarOpt = NONE
fun unT (T xs) = SOME xs
  | unT _ = NONE

fun unR (R v) = SOME v
  | unR _ = NONE

fun pp v =
    case v of
        R r => Real.toString r
      | T vs => "(" ^ String.concatWith "," (map pp vs) ^ ")"

fun lift2 c dc f : v*v->v =
    fn (a,b) => c(f(dc a, dc b))
fun lift1 c dc f : v -> v =
    fn a => c(f(dc a))

val lift2R : (real*real->real) -> (v*v->v) =
    lift2 R (fn R r => r | v => die ("type error - expecting real - 2R - got " ^ pp v))
val lift1R : (real->real) -> (v->v) =
    lift1 R (fn R r => r | v => die ("type error - expecting real - 1R - got " ^ pp v))

fun liftP (s:string) (f: v*v->v) : v -> v =
    fn T [x1,x2] => f (x1,x2)
     | v => die ("type error liftP - expecting pair (" ^ s ^ ") - got " ^ pp v)

fun prjI (s:string) (i:int) : v -> v =
    fn T xs => (List.nth(xs,i-1) handle _ => die (s ^ " index error"))
     | v => die ("type error prjI - expecting tuple (" ^ s ^ ") - got " ^ pp v)

val add = liftP "add" (lift2R (op +))
fun uprim (p: Prim.uprim) : v -> v =
    fn v =>
       case unR v of
           SOME r => R(Prim.uprim p r)
         | NONE => die "type error in uprim - expecting real"

fun uprim_diff (p: Prim.uprim) : v -> v =
    case p of
        Prim.Sin => lift1R (~ o Math.cos)
      | Prim.Cos => lift1R Math.sin
      | Prim.Ln => lift1R (fn x => Math.pow(x,~1.0))
      | Prim.Exp => lift1R Math.exp
      | Prim.Neg => lift1R Real.~
      | Prim.Pow r => lift1R (fn x => r * Math.pow(x,r-1.0))

local
  val mul = lift2R (op * )
in
fun sprod (R s,T vs) =
    let fun unR (R r) = r
          | unR _ = die "sprod expects elements to be reals"
    in T(map R (Prim.sprod (s,map unR vs)))
    end
  | sprod _ = die "sprod expects tuple"

fun dprod (T vs1, T vs2) : v =
    let fun unR (R r) = r
          | unR _ = die "dprod expects elements to be reals"
    in R(Prim.dprod (map unR vs1, map unR vs2))
    end
  | dprod _ = die "dprod expects tuples"

fun cprod3 (T [R a1,R a2,R a3], T [R b1,R b2,R b3]) : v =
    T(map R (Prim.cprod3([a1,a2,a3],[b1,b2,b3])))
  | cprod3 _ = die "cprod3 expects two triples of reals"

fun norm2sq (R x,R y) : v = R(Prim.norm2sq(x,y))
  | norm2sq _ = die "norm2sq expects two real values"

fun bilin (p,v) = liftP (Prim.pp_bilin p) (case p of
                                               Prim.Cprod3 => cprod3
                                             | Prim.Dprod => dprod
                                             | Prim.Sprod => sprod
                                             | Prim.Mul => mul
                                             | Prim.Norm2Sq => norm2sq) v

fun isComplex _ = false

type 'a M = 'a
val ret : 'a -> 'a M = fn x => x
val >>= : 'a M * ('a -> 'b M) -> 'b M = fn (v, f) => f v
val letBind : v -> v M = fn x => x

fun ppM (ind:string) (pp:'a -> string) (x: 'a M) : string = ind ^ pp x

val getVal = fn x => x
end

fun eq (R r, R r') = Real.==(r,r')
  | eq (T vs,T vs') = (List.all eq (ListPair.zip(vs,vs'))
                       handle _ => false)
  | eq _ = false
end (* Val *)

structure TermVal = struct
type var = string
datatype v = R of real | T of v list | Uprim of Prim.uprim * v
           | Add of v*v | Var of var | Bilin of Prim.bilin * v * v

val VarOpt = SOME Var

fun unT (T xs) = SOME xs
  | unT _ = NONE

fun unR (R v) = SOME v
  | unR _ = NONE

fun pp v =
    case v of
        R r => Real.toString r
      | T vs => "(" ^ String.concatWith "," (map pp vs) ^ ")"
      | Uprim(p,v) => Prim.pp_uprim p ^ "(" ^ pp v ^ ")"
      | Add(v1,v2) => "(" ^ pp v1 ^ " + " ^ pp v2 ^ ")"
      | Bilin(p,v1,v2) => "(" ^ pp v1 ^ " " ^ Prim.pp_bilin p ^ " " ^ pp v2 ^ ")"
      | Var v => v

fun prjI (s:string) (i:int) : v -> v =
    fn T xs => (List.nth(xs,i-1) handle _ => die (s ^ " index error"))
     | v => die ("type error prjI - expecting tuple (" ^ s ^ ") - got " ^ pp v)

exception Stop
fun add v =
    case unT v of
        SOME [R a,R b] => R (a+b)
      | SOME [T v1,T v2] =>
        (let fun unR (R r) = r
               | unR _ = raise Stop
         in T(map (R o op+) (ListPair.zip (map unR v1,map unR v2)))
         end handle Stop => Add(T v1,T v2))
      | SOME [v1,v2] => Add(v1,v2)
      | _ => die ("type error add - expecting pair - got " ^ pp v)

fun mul (R a,R b) = R (a*b)
  | mul (T vs1,T vs2) = T (map mul (ListPair.zip (vs1,vs2)))
  | mul (v1,v2) = Bilin(Prim.Mul,v1,v2)

fun cprod3 (T [R a1,R a2,R a3], T [R b1,R b2,R b3]) : v =
    T(map R (Prim.cprod3([a1,a2,a3],[b1,b2,b3])))
  | cprod3 (a,b) = Bilin(Prim.Cprod3,a,b)

exception Stop
fun dprod (T vs1, T vs2) : v =
    (let fun unR (R r) = r
           | unR _ = raise Stop
     in R(Prim.dprod (map unR vs1, map unR vs2))
     end handle Stop => Bilin(Prim.Dprod,T vs1,T vs2))
  | dprod (a,b) = Bilin(Prim.Dprod,a,b)

fun sprod (R s,T vs) =
    (let fun unR (R r) = r
           | unR _ = raise Stop
     in T(map R (Prim.sprod (s,map unR vs)))
     end handle Stop => Bilin(Prim.Sprod,R s,T vs))
  | sprod (R s, R v) = R(s*v)
  | sprod (s,v) = Bilin(Prim.Sprod,s,v)

fun norm2sq (R x,R y) : v = R(Prim.norm2sq(x,y))
  | norm2sq _ = die "norm2sq expects two real values"

fun bilin0 p : v * v -> v =
    case p of
        Prim.Cprod3 => cprod3
      | Prim.Dprod => dprod
      | Prim.Sprod => sprod
      | Prim.Mul => mul
      | Prim.Norm2Sq => norm2sq

fun uprim (p: Prim.uprim) : v -> v =
    fn R r => R (Prim.uprim p r)
     | T vs => T (map (uprim p) vs)
     | v => Uprim (p,v)

val var = Var

local val t = ref 0
in fun tick_reset() = t := 0
   fun tick() = t:= !t + 1
   fun tick_read() = !t
end

fun simpl0 v =
    case v of
        Add(R r1,R r2) => (tick(); R (r1+r2))
      | Add(R r,v) => if Real.==(r,0.0) then (tick(); simpl0 v)
                      else Add(R r,simpl0 v)
      | Add(v,R r) => if Real.==(r,0.0) then (tick(); simpl0 v)
                      else Add(simpl0 v,R r)
      | Add(T vs1,T vs2) => (tick(); T(map (fn (v1,v2) => simpl0 (Add(v1,v2))) (ListPair.zip(vs1,vs2))))
      | Add(v1,v2) => Add(simpl0 v1,simpl0 v2)
      | Uprim (Prim.Pow r,v) =>
        if Real.==(r,1.0) then (tick(); simpl0 v)
        else if Real.==(r,0.0) then (tick(); R 1.0)
        else Uprim(Prim.Pow r, simpl0 v)
      | Uprim (Prim.Neg, R r) => (tick(); R (~r))
      | Uprim (Prim.Neg, T vs) => (tick(); T (map (fn v => simpl0(Uprim(Prim.Neg, v))) vs))
      | Uprim (Prim.Neg, v) => Uprim(Prim.Neg, simpl0 v)
      | Uprim (p,v) => Uprim(p, simpl0 v)
      | T vs => T (map simpl0 vs)
      | R _ => v
      | Var _ => v
      | Bilin(Prim.Mul,R r1,R r2) => (tick(); R (r1*r2))
      | Bilin(Prim.Mul,R r,v) => if Real.==(r,0.0) then (tick(); R 0.0)
                                 else if Real.==(r,1.0) then (tick(); simpl0 v)
                                 else Bilin(Prim.Mul,R r,simpl0 v)
      | Bilin(Prim.Mul,v,R r) => if Real.==(r,0.0) then (tick(); R 0.0)
                                 else if Real.==(r,1.0) then (tick(); simpl0 v)
                                 else Bilin(Prim.Mul,simpl0 v,R r)
      | Bilin(Prim.Mul,v1,v2) => Bilin(Prim.Mul,simpl0 v1,simpl0 v2)
      | Bilin(p,v1,v2) => Bilin(p,simpl0 v1,simpl0 v2)

fun simpl1 e =
    let val () = tick_reset()
        val e' = simpl0 e
    in if tick_read() > 0 then simpl1 e'
       else e'
    end

fun eq (a,b) =
    case (a,b) of
        (R a, R b) => abs (a-b) < 0.0000001
      | (T vs1, T vs2) => List.all (fn x => x) (List.map eq (ListPair.zip (vs1,vs2)))
      | (Var v, Var v') => v=v'
      | (Uprim (p, v), Uprim (p',v')) => Prim.eq_uprim (p,p') andalso eq (v, v')
      | (Add (v1,v2), Add(v1',v2')) => eq(v1,v1') andalso eq(v2,v2')
      | (Bilin (p,v1,v2),Bilin (p',v1',v2')) => Prim.eq_bilin(p,p') andalso eq(v1,v1') andalso eq(v2,v2')
      | _ => false

fun subst S e =
    case e of
        Var k =>
        (case List.find (fn (k0,_) => k=k0) S of
             SOME (k0,v0) => v0
           | NONE => e)
      | R _ => e
      | T es => T(map (subst S) es)
      | Uprim(p,e) => Uprim(p,subst S e)
      | Add(e1,e2) => Add(subst S e1, subst S e2)
      | Bilin(p,e1,e2) => Bilin(p,subst S e1, subst S e2)

fun combine S ca nil = (S,ca)
  | combine S ca ((k,v)::rest) =
    let val v = subst S v
        val v = simpl1 v
    in case List.find (fn (_,v0) => eq (v,v0)) ca of
           SOME (k0,v0) =>
           let val S' = (k,Var k0)::S
           in combine S' ca rest
           end
         | NONE =>
           case v of
               Var _ => combine ((k,v)::S) ca rest
             | R _ => combine ((k,v)::S) ca rest
             | _ => combine S (ca@[(k,v)]) rest
    end

fun simpl (e,bs) =
    let val (S,bs) = combine nil nil bs
    in (simpl1 (subst S e), bs)
    end

fun bilin (p,v:v) : v =
    case unT v of
        SOME [v1,v2] => bilin0 p (v1,v2)
      | _ => die ("type error bilin (" ^ Prim.pp_bilin p ^ ") - expecting pair - got " ^ pp v)

fun uprim_diff (p: Prim.uprim) (x:v) : v =
    case p of
        Prim.Sin => uprim Prim.Neg (uprim Prim.Cos x)
      | Prim.Cos => uprim Prim.Sin x
      | Prim.Ln => uprim (Prim.Pow ~1.0) x
      | Prim.Exp => uprim Prim.Exp x
      | Prim.Neg => uprim Prim.Neg x
      | Prim.Pow r => bilin0 Prim.Mul (R r,uprim (Prim.Pow(r-1.0)) x)

fun isComplex v =
    case v of
        R _ => false
      | Var _ => false
      | T vs => false
      | Uprim (p,v) => true
      | Add _ => true
      | Bilin _ => true

type 'a M = 'a * (string * v)list

val newVar =
    let val c = ref 0
    in fn () => (c:= !c + 1; "v" ^ Int.toString (!c))
    end

infix >>=
fun ((a,ca) : 'a M) >>= (f: 'a -> 'b M) : 'b M =
    let val (b,cb) = f a
        (*val (S,c) = combine nil ca cb*)
    in (b,ca@cb)
    end
fun ret (x:'a) = (x,nil)

fun letBind (v:v) : v M =
    if isComplex v then
      let val var = newVar()
      in (Var var, [(var,v)])
      end
    else ret v

fun ppM (ind:string) (pp0:'a -> string) ((x,bs): 'a M) : string =
    case bs of
        nil => ind ^ pp0 x
      | _ => let val bs = List.map (fn (var,v) => ind ^ "let " ^ var ^ " = " ^ pp v) bs
             in String.concatWith "\n" bs ^ "\n" ^ ind ^ "in " ^ pp0 x
             end

val getVal = fn (x,_) => x

end (* TermVal *)


signature FUN = sig
  type v
  datatype f =
         Comp of f * f       (* X -> Y *)
       | Prj of int          (* X1*...*Xn->Xi *)
       | Add                 (* R*R->R *)
       | K of v              (* X -> Y *)
       | FProd of f * f      (*A*B->C*D*)
       | Dup                 (* X->X*X *)
       | Id                  (* X -> X *)
       | Uprim of Prim.uprim
       | Bilin of Prim.bilin (* X*Y->Z *)

  val pp  : f -> string
  val opt : f -> f
  structure DSL : sig
    val x : f * f -> f
    val + : f
    val * : f
    val o : f * f -> f
    val sin  : f
    val cos  : f
    val exp  : f
    val ln   : f
    val pow  : real -> f
    val ~    : f
    val dup  : f
    val id   : f
  end
end

functor Fun(V:VAL) :> FUN where type v = V.v = struct

type v = V.v
datatype f =
         Comp of f * f       (* X -> Y *)
       | Prj of int          (* X1*...*Xn->Xi *)
       | Add                 (* R*R->R *)
       | K of V.v            (* X -> Y *)
       | FProd of f * f      (*A*B->C*D*)
       | Dup                 (* X->X*X *)
       | Id                  (* X -> X *)
       | Uprim of Prim.uprim
       | Bilin of Prim.bilin

fun pp e =
    case e of
        Comp(f,g) => "(" ^ pp f ^ " o " ^ pp g ^ ")"
      | Id => "id"
      | Prj i => "pi" ^ Int.toString i
      | Add => "(+)"
      | K v => V.pp v
      | FProd(f,g) => "(" ^ pp f ^ " x " ^ pp g ^ ")"
      | Dup => "dup"
      | Uprim p => Prim.pp_uprim p
      | Bilin opr => "(" ^ Prim.pp_bilin opr ^ ")"

local val t = ref 0
in fun tick_reset() = t := 0
   fun tick() = t:= !t + 1
   fun tick_read() = !t
end

fun opt0 e =
    case e of
        Comp(FProd(Prj 1,Prj 2),Dup) => (tick(); Id)
      | Comp(Id,f) => (tick(); opt0 f)
      | Comp(f,Id) => (tick(); opt0 f)
      | Comp(f,g) => Comp(opt0 f,opt0 g)
      | FProd(f,g) => FProd(opt0 f,opt0 g)
      | _ => e

fun opt e =
    let val () = tick_reset()
        val e' = opt0 e
    in if tick_read() > 0 then opt e'
       else e'
    end

structure DSL = struct
  val op x = FProd
  val op + = Add
  val op * = Bilin Prim.Mul
  val op o = Comp
  val dup = Dup
  val id = Id
  val sin = Uprim Prim.Sin
  val cos = Uprim Prim.Cos
  val exp = Uprim Prim.Exp
  val ln = Uprim Prim.Ln
  fun pow r = Uprim (Prim.Pow r)
  val ~ = Uprim Prim.Neg
end
end (* Fun *)

signature LIN = sig
  type v
  type lin
  type 'a M

  (* Constructors *)
  val lin   : string * (v -> v) -> lin
  val prj   : int -> lin
  val zero  : lin
  val id    : lin
  val oplus : lin * lin -> lin
  val comp  : lin * lin -> lin
  val curL  : Prim.bilin * v -> lin
  val curR  : Prim.bilin * v -> lin

  val pp    : lin -> string
  val eval  : lin -> v -> v M
end

functor Lin(V:VAL) :> LIN where type v = V.v and type 'a M = 'a V.M = struct
type v = V.v
type 'a M = 'a V.M

datatype lin = Lin of string * (v -> v)
             | Prj of int
             | Zero
             | Id
             | Oplus of lin * lin
             | Comp of lin * lin
             | CurL of Prim.bilin * v
             | CurR of Prim.bilin * v

val lin = Lin
val prj = Prj
val zero = Zero
val id = Id
val oplus = Oplus
val comp = Comp
val curL = CurL
val curR = CurR

fun pp e =
    case e of
        Lin("add",_) => "(+)"
      | Lin(s,_) => s
      | Prj i => "pi" ^ Int.toString i
      | Zero => "zero"
      | Id => "id"
      | Oplus(e1,e2) => "(" ^ pp e1 ^ " :+: " ^ pp e2 ^ ")"
      | Comp(e1,e2) => pp e1 ^ " :o: " ^ pp e2
      | CurL(p,v) => "(" ^ V.pp v ^ " " ^ Prim.pp_bilin p ^ ")"
      | CurR(p,v) => "(" ^ Prim.pp_bilin p ^ " " ^ V.pp v ^ ")"

val ret = V.ret
infix >>=
val op >>= = V.>>=
val letBind = (*V.letBind*) ret

fun eval (e:lin) (x:v) : v V.M =
    case e of
        Zero => ret (V.R 0.0)
      | Id => ret x
      | Lin(s,f) => (letBind (f x) handle X => (print ("Lin problem: " ^ s ^ "; x=" ^ V.pp x ^ "\n"); raise X))
      | Prj i => ret (V.prjI "eval projection error" i x)
      | Oplus(f,g) =>
        (case V.unT x of
             SOME [x,y] => eval f x >>= (fn v1 =>
                           eval g y >>= (fn v2 =>
                           letBind (V.T[v1,v2])))
           | _ => die ("eval.Oplus: expecting pair - got " ^ V.pp x))
      | Comp(g,f) => eval f x >>= eval g
      | CurL(p,v) => letBind (V.bilin (p,V.T[v,x]) handle X => (print ("CurL problem: " ^ Prim.pp_bilin p ^ "; v=" ^
                                                                       V.pp v ^ "; x=" ^ V.pp x ^ "\n"); raise X))
      | CurR(p,v) => letBind (V.bilin (p,V.T[x,v]) handle X => (print ("CurR problem: " ^ Prim.pp_bilin p ^ "; x=" ^
                                                                       V.pp x ^ "; v=" ^ V.pp v ^ "\n"); raise X))
end

signature DIFF = sig
  type v
  structure L : LIN where type v = v
  structure F : FUN where type v = v
  val diff : F.f -> v -> v * L.lin
end

functor Diff(V:VAL) : DIFF where type v = V.v = struct
structure F = Fun(V)
structure L = Lin(V)
type v = V.v

fun diff (f:F.f) (x:v) : v * L.lin =
    case f of
        F.Comp(g,f) =>
        let val (fx,f'x) = diff f x
            val (gfx,g'fx) = diff g fx
        in (gfx,L.comp(g'fx,f'x))
        end
      | F.K y => (y, L.zero)
      | F.Add =>
        let val h = V.add
        in (h x, L.lin("add",h))
        end
      | F.Uprim p => (V.uprim p x,
                      L.curL (Prim.Mul,V.uprim_diff p x))
      | F.Prj i =>
        let val h = V.prjI ("Prj" ^ Int.toString i) i
        in (h x, L.prj i)
        end
      | F.Dup =>
        let val h = fn v => V.T[v,v]
        in (h x, L.lin("dup",h))
        end
      | F.FProd(f,g) =>
        let val (fx,f'x) = diff f (V.prjI "fprod-x" 1 x)
            val (gy,g'y) = diff g (V.prjI "fprod-y" 2 x)
        in (V.T[fx,gy],L.oplus(f'x,g'y))
        end
      | F.Bilin p =>
        (V.bilin (p,x),
         L.comp(L.lin ("add",V.add),
                L.oplus(L.curR(p,V.prjI "mul-R" 2 x),
                        L.curL(p,V.prjI "mul-L" 1 x))))
      | F.Id => (x, L.id)
end

functor Exp(structure V:VAL
            structure F:FUN
            sharing type V.v = F.v) = struct
type v = V.v
datatype e =
         X of int
       | C of v
       | Uprim of Prim.uprim * e
       | Bilin of Prim.bilin * e * e
       | Add of e * e
       | Pair of e * e

fun pp e =
    case e of
        X i => "x" ^ Int.toString i
      | C v => V.pp v
      | Uprim(p,e) => Prim.pp_uprim p ^ "(" ^ pp e ^ ")"
      | Bilin(p,e1,e2) => "(" ^ pp e1 ^ Prim.pp_bilin p ^ pp e2 ^ ")"
      | Add(e1,e2) => "(" ^ pp e1 ^ "+" ^ pp e2 ^ ")"
      | Pair(e1,e2) => "(" ^ pp e1 ^ "," ^ pp e2 ^ ")"

fun lrangle (f,g) = F.Comp(F.FProd(f,g),F.Dup)
fun hat opr (f,g) = F.Comp(opr,lrangle(f,g))

fun trans e =
    case e of
        X i => F.Prj i
      | C v => F.K v
      | Uprim(p,e) => F.Comp (F.Uprim p, trans e)
      | Bilin(p,e1,e2) => hat (F.Bilin p) (trans e1,trans e2)
      | Add(e1,e2) => hat F.Add (trans e1,trans e2)
      | Pair(e1,e2) => lrangle (trans e1,trans e2)

structure DSL = struct
  val ln : e -> e = fn e => Uprim(Prim.Ln,e)
  val sin : e -> e = fn e => Uprim(Prim.Sin,e)
  val cos : e -> e = fn e => Uprim(Prim.Cos,e)
  val exp : e -> e = fn e => Uprim(Prim.Exp,e)
  fun pow (r: real) : e -> e = fn e => Uprim(Prim.Pow r,e)
  val ~ : e -> e = fn e => Uprim(Prim.Neg,e)
  val op + : e * e -> e = Add
  val op * : e * e -> e = fn (x,y) => Bilin(Prim.Mul,x,y)
  val op - : e * e -> e  = fn (x,y) => x + (~y)
  val x1 : e = X 1
  val x2 : e = X 2
end
end
  ;

functor Ex0(V:VAL) : sig end = struct
structure D = Diff(V)
structure F = D.F
structure E = Exp(structure V = V
                  structure F = F)
structure L = D.L


fun pp_expected expected (sel: V.v*V.v->V.v) (v:V.v) : string =
    case expected of NONE => ""
                   | SOME p => if V.eq(v,sel p) then ": OK"
                               else (": WRONG - expected " ^ V.pp v ^ " - got " ^ V.pp (sel p))

fun try_ex {name, e, arg, d, expected} =
    let val () = print ("\nTrying example: " ^ name ^ "\n")
        val () = print ("  e = " ^ E.pp e ^ "\n")
        val f1 = E.trans e
        val () = print ("  f_unopt = " ^ F.pp f1 ^ "\n")
        val f = F.opt f1
        val () = print ("  f = " ^ F.pp f ^ "\n")
        val (r,l) = D.diff f arg
        val () = print ("  f(" ^ V.pp arg ^ ") = " ^ V.pp r ^ pp_expected expected (#1) r ^ "\n")
        val () = print ("  f'(" ^ V.pp arg ^ ") = " ^ L.pp l ^ "\n")
        val rM = L.eval l d
        val () = print ("  f'(" ^ V.pp arg ^ ")(" ^ V.pp d ^ ") =\n" ^
                        V.ppM "    " V.pp rM ^ pp_expected expected (#2) (V.getVal rM) ^ "\n")
    in ()
    end

fun try_fun {name, f, arg, d, expected} =
    let val () = print ("\nTrying fun example: " ^ name ^ "\n")
        val () = print ("  f = " ^ F.pp f ^ "\n")
        val (r,l) = D.diff f arg
        val () = print ("  f(" ^ V.pp arg ^ ") = " ^ V.pp r ^ "\n")
        val () = print ("  f'(" ^ V.pp arg ^ ") = " ^ L.pp l ^ "\n")
        val rM = L.eval l d
        val () = print ("  f'(" ^ V.pp arg ^ ")(" ^ V.pp d ^ ") =\n" ^
                        V.ppM "    " V.pp rM ^ pp_expected expected (#2) (V.getVal rM) ^ "\n")
    in ()
    end

local open E.DSL
in
val () = try_ex {name="ex1", e=ln (sin x1), arg=V.T[V.R 3.0], d=V.T[V.R 1.0],expected=SOME(V.R ~1.95814462961,V.R 7.01525255143)}
val () = try_ex {name="ex2", e=x1*x2, arg=V.T[V.R 3.0,V.R 1.0], d=V.T[V.R 1.0,V.R 0.0],expected=SOME(V.R 3.0,V.R 1.0)}
val () = try_ex {name="ex3", e=ln x1 + x1*x2 - sin x2, arg=V.T[V.R 3.0,V.R 1.0], d=V.T[V.R 1.0,V.R 0.0],expected=SOME(V.R 3.25714130386, V.R 1.33333333333)}
end

local open F.DSL
      infix x nonfix + nonfix *
in
val () = try_fun {name="fun1", f=(id x ln) o dup o (+) o (cos x sin),arg=V.T[V.R 1.5,V.R 2.0],d=V.T[V.R 2.0,V.R 2.0],
                  expected=SOME(V.T[V.R 0.980034628493,V.R ~0.0201673727445],
                                V.T[V.R 2.8272836463,V.R 2.8848813747])}
end
end

structure Ex0_Val = Ex0(Val)

structure Ex0_TermVal = Ex0(TermVal)

structure Ex1 : sig end = struct
structure V = TermVal
structure D = Diff(V)
structure F = D.F
structure E = Exp(structure V = V
                  structure F = F)
structure L = D.L
fun try_ex {name, e, arg, d} =
    let val () = print ("\nTrying example: " ^ name ^ "\n")
        val () = print ("  e = " ^ E.pp e ^ "\n")
        val f1 = E.trans e
        val () = print ("  f_unopt = " ^ F.pp f1 ^ "\n")
        val f = F.opt f1
        val () = print ("  f = " ^ F.pp f ^ "\n")
        val (r,l) = D.diff f arg
        val () = print ("  f(" ^ V.pp arg ^ ") = " ^ V.pp r ^ "\n")
        val () = print ("  f'(" ^ V.pp arg ^ ") = " ^ L.pp l ^ "\n")
        val rM = L.eval l d
        val rM = V.simpl rM
        val () = print ("  f'(" ^ V.pp arg ^ ")(" ^ V.pp d ^ ") =\n" ^
                        V.ppM "    " V.pp rM ^ "\n")
    in ()
    end

fun try_fun {name, f, arg, d} =
    let val () = print ("\nTrying example: " ^ name ^ "\n")
        val () = print ("  " ^ name ^ " = " ^ F.pp f ^ "\n")
        val (r,l) = D.diff f arg
        val () = print ("  " ^ name ^ "(" ^ V.pp arg ^ ") = " ^ V.pp r ^ "\n")
        val () = print ("  " ^ name ^ "'(" ^ V.pp arg ^ ") = " ^ L.pp l ^ "\n")
        val () = print "Now evaluating\n"
        val rM = L.eval l d
        val () = print "Now simplifying\n"
        val rM = V.simpl rM
        val () = print ("  " ^ name ^ "'(" ^ V.pp arg ^ ")(" ^ V.pp d ^ ") =\n" ^
                        V.ppM "    " V.pp rM ^ "\n")
    in ()
    end

local open E.DSL
in
val () = try_ex {name="t1", e=ln (sin x1), arg=V.T[V.Var "x1"], d=V.T[V.R 1.0]}
val () = try_ex {name="t2", e=x1*x2, arg=V.T[V.Var "x1",V.Var "x2"], d=V.T[V.R 1.0,V.R 0.0]}
val () = try_ex {name="t3", e=ln x1 + x1*x2 - sin x2, arg=V.T[V.Var "x1",V.Var "x2"], d=V.T[V.R 1.0,V.R 0.0]}
end

local open F.DSL
      infix x nonfix + nonfix *
in
val () = try_fun {name="fun1", f=(id x ln) o dup o (+) o (cos x sin),arg=V.T[V.Var "x1",V.Var "x2"],d=V.T[V.R 2.0,V.R 2.0]}
                 (* f'((x1,x2)) = (id :+: (pow(~1.0)((cos(x1) + sin(x2)))* )) :o: dup :o: (+) :o: ((sin(x1)* ) :+: (~(cos(x2))* )) *)
val () = try_fun {name="fun2", f=ln,arg=V.T[V.Var "x1"],d=V.T[V.R 2.0]}

val Dot = F.Bilin Prim.Dprod
val Norm2Sq = F.Bilin Prim.Norm2Sq
infix vscale cross dot norm2sq
fun f vscale g = F.Bilin Prim.Sprod o (f x g) o dup
fun f cross g = F.Bilin Prim.Cprod3 o (f x g) o dup
fun f norm2sq g = F.Bilin Prim.Norm2Sq o (f x g) o dup
fun f dot g = Dot o (f x g) o dup
infix +
val op + = fn (f,g) => (op +) o (f x g) o dup
val K1 = F.K (V.R 1.0)
val norm = pow 0.5 o Dot o dup
val nrm = (pow ~1.0 o norm) vscale id
val () = try_fun {name="norm", f=norm,arg=V.Var "x",d=V.Var "dx1"}
val () = try_fun {name="norm", f=norm,arg=V.T[V.R 3.0,V.R 4.0],d=V.T[V.R 1.0,V.R 0.0]}
val () = try_fun {name="nrm", f=nrm,arg=V.Var "x",d=V.Var "dx1"}
val () = try_fun {name="nrm", f=nrm,arg=V.T[V.Var "x1",V.Var "x2",V.Var "x3"],
                  d=V.T[V.Var "dx1",V.Var "dx2",V.Var "dx3"]}
val () = try_fun {name="nrm", f=nrm,arg=V.T[V.R 2.0,V.R 3.0,V.R 5.0],
                  d=V.T[V.R 1.0,V.R 0.0,V.R 0.0]}

val rodriguez =
    let val pi_r = F.Prj 1
        val pi_X = F.Prj 2
    in ((cos o norm o pi_r) vscale pi_X) +
       ((sin o norm o pi_r) vscale ((nrm o pi_r) cross pi_X)) +
       ((K1 + (~ o cos o norm o pi_r)) vscale (((nrm o pi_r) dot (nrm o pi_r)) vscale pi_X))
    end

val r = V.T[V.R 1.0, V.R 2.6, V.R 3.0]
val X = V.T[V.R 10.0, V.R 20.6, V.R 30.0]
val () = try_fun {name="rodriguez", f=rodriguez,arg=V.T[V.Var "r",V.Var "X"],d=V.T[V.Var "dr",V.Var "dX"]}
val () = try_fun {name="rodriguez", f=rodriguez,arg=V.T[r,X],d=V.T[r,X]}

val p2e =
    let val pi_1 = F.Prj 1
        val pi_2 = F.Prj 2
        val pi_3 = F.Prj 3
    in (pow ~1.0 o pi_3) vscale ((pi_1 x pi_2) o dup)
    end

val arg = V.T[V.R 6.0, V.R 12.0, V.R 3.0]
val () = try_fun {name="p2e", f=p2e,arg=arg,d=V.T[V.R 1.0,V.R 0.0,V.R 0.0]}

val distort =
    let val pi_1 = F.Prj 1
        val pi_2 = F.Prj 2
        val pi_k = F.Prj 1
        val pi_X = F.Prj 2
    in ((K1 + (Norm2Sq o pi_X) vscale (pi_1 o pi_k)) +
       ((pow 2.0 o Norm2Sq o pi_X) vscale (pi_2 o pi_k))) vscale pi_k
    end
val () = try_fun {name="distort", f=distort,
                  arg=V.T[V.T[V.R 2.0,V.R 3.0],V.T[V.R 8.0,V.R 9.0]],
                  d=V.T[V.T[V.R 2.0,V.R 3.0],V.T[V.R 8.0,V.R 9.0]]}

fun lrangle (f,g) = F.Comp(F.FProd(f,g),F.Dup)

val project (* -> R^2 *) =
    let val pi_r = F.Prj 1    (* R^3 *)
        val pi_C = F.Prj 2    (* R^3 *)
        val pi_f = F.Prj 3    (* R   *)
        val pi_x0 = F.Prj 4   (* R^2 *)
        val pi_k = F.Prj 5    (* R^2 *)
        val pi_X = F.Prj 6    (* R^3 *)
    in pi_f vscale (distort o lrangle (pi_k, p2e o rodriguez o lrangle (pi_r, pi_X + (~ o pi_C))))
       + pi_x0
    end

val r = V.T[V.R 2.0, V.R 3.0, V.R 8.0]
val C = V.T[V.R 1.0, V.R 2.0, V.R 6.0]
val f = V.R 3.0
val x0 = V.T[V.R 1.0, V.R 2.0]
val k = V.T[V.R 2.0, V.R 3.0]
val X = V.T[V.R 6.0, V.R 9.0, V.R 2.0]

val () = try_fun {name="project", f=project,
                  arg=V.T[r,C,f,x0,k,X],
                  d=V.T[r,C,f,x0,k,X]}

val residual (* -> R^2 *) =
    let val pi_w = F.Prj 1    (* R *)
        val pi_m = F.Prj 2    (* R^2 *)
        val pi_P = F.Prj 3    (* R^3*R^3*R*R^2*R^2*R^3 *)
    in lrangle (pi_w vscale (pi_m + ~ o project o pi_P), K1 + ~ o pow 2.0 o pi_w)
    end

val P = V.T[r,C,f,x0,k,X]
val dP = V.T[r,C,f,x0,k,X]
val w = V.R 1.2
val m = V.T[V.R 1.0,V.R 2.0]

val dw = V.R 0.2
val dm = V.T[V.R 0.3,V.R 1.0]

val () = try_fun {name="residual", f=residual,
                  arg=V.T[w,m,P],
                  d=V.T[dw,dm,dP]}

end

end
