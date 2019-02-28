(* Dynamically tagged version of combinatory differentiation interpretation (in SML)
 *
 * Todo:
 *  1) Evaluate Lin expressions
 *  2) Experiment with forward/reverse mode differences
 *  3) Instead of evaluating expressions, I believe we can build up
 *     expressions parameterised over the input variables (at least when
 *     we don't try to differentiate conditional expressions, recursion,
 *     and such...
 *
 * Questions:
 *  1) Can we somehow convert point-free notation to expressions with let-expressions?
 *)

fun die s = (print ("Error: " ^ s ^ "\n"); raise Fail s)

signature VAL = sig
  type v
  val R   : real -> v
  val I   : int -> v
  val T   : v list -> v

  val unT : v -> v list option
  val pp : v -> string
  val prjI : string -> int -> v -> v
  val add : v -> v
  val sin : v -> v
  val cos : v -> v
  val ln  : v -> v
  val exp : v -> v
  val neg : v -> v
  val pow : int -> v -> v
  val mul : v -> v
end

structure Val :> VAL = struct
datatype v = R of real | I of int | T of v list

fun unT (T xs) = SOME xs
  | unT _ = NONE

fun pp v =
    case v of
        R r => Real.toString r
      | I i => Int.toString i
      | T vs => "(" ^ String.concatWith "," (map pp vs) ^ ")"

fun lift2 c dc f : v*v->v =
    fn (a,b) => c(f(dc a, dc b))
fun lift1 c dc f : v -> v =
    fn a => c(f(dc a))

val lift2R : (real*real->real) -> (v*v->v) =
    lift2 R (fn R r => r | v => die ("type error - expecting real - 2R - got " ^ pp v))
val lift1R : (real->real) -> (v->v) =
    lift1 R (fn R r => r | v => die ("type error - expecting real - 1R - got " ^ pp v))

val lift2I : (int*int->int) -> (v*v->v) =
    lift2 I (fn I i => i | _ => die "type error - expecting int")
val lift1I : (int->int) -> (v->v) =
    lift1 I (fn I i => i | _ => die "type error - expecting int")

fun liftP (s:string) (f: v*v->v) : v -> v =
    fn T [x1,x2] => f (x1,x2)
     | v => die ("type error liftP - expecting pair (" ^ s ^ ") - got " ^ pp v)

fun prjI (s:string) (i:int) : v -> v =
    fn T xs => (List.nth(xs,i-1) handle _ => die (s ^ " index error"))
     | v => die ("type error prjI - expecting tuple (" ^ s ^ ") - got " ^ pp v)

val add = liftP "add" (lift2R (op +))
val sin = lift1R Math.sin
val cos = lift1R Math.cos
val ln = lift1R Math.ln
val exp = lift1R Math.exp
val neg = lift1R Real.~
fun pow i = lift1R (fn x => Math.pow(x,real i))
val mul = liftP "mul" (lift2R (op * ))
end (* Val *)

structure TermVal = struct
type var = string
datatype v = R of real | I of int | T of v list | Sin of v | Cos of v | Ln of v | Exp of v
           | Neg of v | Mul of v*v | Add of v*v | Pow of int * v | Var of var

fun unT (T xs) = SOME xs
  | unT _ = NONE

fun pp v =
    case v of
        R r => Real.toString r
      | I i => Int.toString i
      | T vs => "(" ^ String.concatWith "," (map pp vs) ^ ")"
      | Sin v => "sin(" ^ pp v ^ ")"
      | Cos v => "cos(" ^ pp v ^ ")"
      | Ln v => "ln(" ^ pp v ^ ")"
      | Exp v => "exp(" ^ pp v ^ ")"
      | Pow(i,v) => "pow(" ^ Int.toString i ^ "," ^ pp v ^ ")"
      | Neg v => "neg(" ^ pp v ^ ")"
      | Add(v1,v2) => "(" ^ pp v1 ^ " + " ^ pp v2 ^ ")"
      | Mul(v1,v2) => "(" ^ pp v1 ^ " * " ^ pp v2 ^ ")"
      | Var v => v

fun prjI (s:string) (i:int) : v -> v =
    fn T xs => (List.nth(xs,i-1) handle _ => die (s ^ " index error"))
     | v => die ("type error prjI - expecting tuple (" ^ s ^ ") - got " ^ pp v)

fun add v =
    case unT v of
        SOME [v1,v2] => Add(v1,v2)
      | _ => die ("type error add - expecting pair - got " ^ pp v)

fun mul v =
    case unT v of
        SOME [v1,v2] => Mul(v1,v2)
      | _ => die ("type error mul - expecting pair - got " ^ pp v)

val sin = Sin
val cos = Cos
val ln = Ln
val exp = Exp
val neg = Neg
fun pow i v = Pow(i,v)
val var = Var

local val t = ref 0
in fun tick_reset() = t := 0
   fun tick() = t:= !t + 1
   fun tick_read() = !t
end

fun simpl0 v =
    case v of
        Add(R r1,R r2) => (tick(); R (r1+r2))
      | Add(I r1,I r2) => (tick(); I (r1+r2))
      | Mul(R r1,R r2) => (tick(); R (r1*r2))
      | Mul(I r1,I r2) => (tick(); I (r1*r2))
      | Add(R r,v) => if Real.==(r,0.0) then (tick(); simpl0 v)
                      else Add(R r,simpl0 v)
      | Add(v,R r) => if Real.==(r,0.0) then (tick(); simpl0 v)
                      else Add(simpl0 v,R r)
      | Mul(R r,v) => if Real.==(r,0.0) then (tick(); R 0.0)
                      else if Real.==(r,1.0) then (tick(); simpl0 v)
                      else Mul(R r,simpl0 v)
      | Mul(v,R r) => if Real.==(r,0.0) then (tick(); R 0.0)
                      else if Real.==(r,1.0) then (tick(); simpl0 v)
                      else Mul(simpl0 v,R r)
      | Mul(v1,v2) => Mul(simpl0 v1,simpl0 v2)
      | Add(v1,v2) => Add(simpl0 v1,simpl0 v2)
      | Sin v => Sin (simpl0 v)
      | Cos v => Cos (simpl0 v)
      | Ln v => Ln (simpl0 v)
      | Exp v => Exp (simpl0 v)
      | Pow(1,v) => (tick(); simpl0 v)
      | Pow(0,_) => (tick(); R 1.0)
      | Pow(i,v) => Pow(i,simpl0 v)
      | Neg(R r) => (tick(); R (~r))
      | Neg(I i) => (tick(); I (~i))
      | Neg v => Neg (simpl0 v)
      | T vs => T (map simpl0 vs)
      | R _ => v
      | I _ => v
      | Var _ => v

fun simpl e =
    let val () = tick_reset()
        val e' = simpl0 e
    in if tick_read() > 0 then simpl e'
       else e'
    end

end (* TermVal *)


signature FUN = sig
  type v
  datatype f =
         Comp of f * f     (* X -> Y *)
       | Ln                (* R -> R *)
       | Exp               (* R -> R *)
       | Sin               (* R -> R *)
       | Cos               (* R -> R *)
       | Pow of int        (* R -> R *)
       | Neg               (* R -> R *)
       | Prj of int        (* X1*...*Xn->Xi *)
       | Add               (* R*R->R *)
       | Mul               (* R*R->R *)
       | K of v            (* X -> Y *)
       | FProd of f * f    (*A*B->C*D*)
       | Dup               (* X->X*X *)
       | Id                (* X -> X *)

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
    val pow  : int -> f
    val ~    : f
    val dup  : f
    val id   : f
  end
end

functor Fun(V:VAL) :> FUN where type v = V.v = struct

type v = V.v
datatype f =
         Comp of f * f     (* X -> Y *)
       | Ln                (* R -> R *)
       | Exp               (* R -> R *)
       | Sin               (* R -> R *)
       | Cos               (* R -> R *)
       | Pow of int        (* R -> R *)
       | Neg               (* R -> R *)
       | Prj of int        (* X1*...*Xn->Xi *)
       | Add               (* R*R->R *)
       | Mul               (* R*R->R *)
       | K of V.v          (* X -> Y *)
       | FProd of f * f    (*A*B->C*D*)
       | Dup               (* X->X*X *)
       | Id                (* X -> X *)

fun pp e =
    case e of
        Comp(f,g) => "(" ^ pp f ^ " o " ^ pp g ^ ")"
      | Id => "id"
      | Ln => "ln"
      | Exp => "exp"
      | Sin => "sin"
      | Cos => "cos"
      | Pow i => "pow(" ^ Int.toString i ^ ")"
      | Neg => "~"
      | Prj i => "pi" ^ Int.toString i
      | Add => "(+)"
      | Mul => "(*)"
      | K v => V.pp v
      | FProd(f,g) => "(" ^ pp f ^ " x " ^ pp g ^ ")"
      | Dub => "dup"

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
  val op * = Mul
  val op o = Comp
  val sin = Sin
  val cos = Cos
  val exp = Exp
  val ln = Ln
  val pow = Pow
  val ~ = Neg
  val dup = Dup
  val id = Id
end
end (* Fun *)

signature LIN = sig
  type v
  type bin = string * (v -> v)
  type lin

  (* Constructors *)
  val lin   : string * (v -> v) -> lin
  val prj   : int -> lin
  val zero  : lin
  val id    : lin
  val oplus : lin * lin -> lin
  val comp  : lin * lin -> lin
  val curL  : bin * v -> lin
  val curR  : bin * v -> lin

  val mulR  : bin

  val pp    : lin -> string
  val eval  : lin -> v -> v
end

functor Lin(V:VAL) :> LIN where type v = V.v = struct
type v = V.v
type bin = string * (v -> v)
datatype lin = Lin of string * (v -> v)
             | Prj of int
             | Zero
             | Id
             | Oplus of lin * lin
             | Comp of lin * lin
             | CurL of bin * v
             | CurR of bin * v

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
      | Lin("mul",_) => "(*)"
      | Lin(s,_) => s
      | Prj i => "pi" ^ Int.toString i
      | Zero => "zero"
      | Id => "id"
      | Oplus(e1,e2) => "(" ^ pp e1 ^ " :+: " ^ pp e2 ^ ")"
      | Comp(e1,e2) => pp e1 ^ " :o: " ^ pp e2
      | CurL(("add",_),v) => "(" ^ V.pp v ^ "+)"
      | CurL(("mul",_),v) => "(" ^ V.pp v ^ "*)"
      | CurL((s,_),v) => "(" ^ V.pp v ^ " " ^ s ^ ")"
      | CurR(("add",_),v) => "(+" ^ V.pp v ^ ")"
      | CurR(("mul",_),v) => "(*" ^ V.pp v ^ ")"
      | CurR((s,_),v) => "(" ^ s ^ " " ^ V.pp v ^ ")"

fun eval (e:lin) (x:v) : v =
    case e of
        Zero => V.R 0.0
      | Id => x
      | Lin(s,f) => (f x handle X => (print ("Lin problem: " ^ s ^ "; x=" ^ V.pp x ^ "\n"); raise X))
      | Prj i => V.prjI "eval projection error" i x
      | Oplus(f,g) =>
        (case V.unT x of
             SOME [x,y] => V.T[eval f x,eval g y]
           | _ => die ("eval.Oplus: expecting pair - got " ^ V.pp x))
      | Comp(g,f) => eval g (eval f x)
      | CurL((s,f),v) => (f(V.T[v,x]) handle X => (print ("CurL problem: " ^ s ^ "; v=" ^
                                                            V.pp v ^ "; x=" ^ V.pp x ^ "\n"); raise X))
      | CurR((s,f),v) => (f(V.T[x,v]) handle X => (print ("CurR problem: " ^ s ^ "; x=" ^
                                                            V.pp x ^ "; v=" ^ V.pp v ^ "\n"); raise X))

val mulR : bin = ("mul", V.mul)
end

functor Diff(V:VAL) = struct
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
      | F.Cos => (V.cos x,
                  L.curL (L.mulR,V.sin x))
      | F.Sin => (V.sin x,
                  L.curL (L.mulR,V.neg (V.cos x)))
      | F.Ln => (V.ln x,
                 L.curL (L.mulR,V.pow (~1) x))
      | F.Exp => (V.exp x,
                  L.curL (L.mulR,V.exp x))
      | F.Pow i => (V.pow i x,
                    L.curL (L.mulR,V.mul(V.T[V.R (real i),V.pow (i-1) x])))
      | F.Neg => (V.neg x,
                  L.curL (L.mulR,V.neg x))
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
      | F.Mul =>
        (V.mul x,
         L.comp(L.lin ("add",V.add),
                L.oplus(L.curR(L.mulR,V.prjI "mul-R" 2 x),
                        L.curL(L.mulR,V.prjI "mul-L" 1 x))))
      | F.Id => (x, L.id)
end

functor Exp(structure V:VAL
            structure F:FUN
            sharing type V.v = F.v) = struct
type v = V.v
datatype e =
         X of int
       | C of v
       | Ln of e
       | Exp of e
       | Sin of e
       | Cos of e
       | Neg of e
       | Pow of int * e
       | Mul of e * e
       | Add of e * e
       | Pair of e * e

fun pp e =
    case e of
        X i => "x" ^ Int.toString i
      | C v => V.pp v
      | Ln e => "ln(" ^ pp e ^ ")"
      | Exp e => "exp(" ^ pp e ^ ")"
      | Sin e => "sin(" ^ pp e ^ ")"
      | Cos e => "cos(" ^ pp e ^ ")"
      | Neg e => "neg(" ^ pp e ^ ")"
      | Pow(i,e) => "pow(" ^ Int.toString i ^ "," ^ pp e ^ ")"
      | Mul(e1,e2) => "(" ^ pp e1 ^ "*" ^ pp e2 ^ ")"
      | Add(e1,e2) => "(" ^ pp e1 ^ "+" ^ pp e2 ^ ")"
      | Pair(e1,e2) => "(" ^ pp e1 ^ "," ^ pp e2 ^ ")"

fun lrangle (f,g) = F.Comp(F.FProd(f,g),F.Dup)
fun hat opr (f,g) = F.Comp(opr,lrangle(f,g))

fun trans e =
    case e of
        X i => F.Prj i
      | C v => F.K v
      | Ln e => F.Comp (F.Ln, trans e)
      | Exp e => F.Comp (F.Exp, trans e)
      | Sin e => F.Comp (F.Sin, trans e)
      | Cos e => F.Comp (F.Cos, trans e)
      | Neg e => F.Comp (F.Neg, trans e)
      | Pow(i,e) => F.Comp(F.Pow i,trans e)
      | Mul(e1,e2) => hat F.Mul (trans e1,trans e2)
      | Add(e1,e2) => hat F.Add (trans e1,trans e2)
      | Pair(e1,e2) => lrangle (trans e1,trans e2)

structure DSL = struct
  val ln : e -> e = Ln
  val sin : e -> e = Sin
  val cos : e -> e = Cos
  val exo : e -> e = Exp
  fun pow (i: int) : e -> e = fn e => Pow(i,e)
  val ~ : e -> e = Neg
  val op + : e * e -> e = Add
  val op * : e * e -> e = Mul
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
        val r' = L.eval l d
        val () = print ("  f'(...)(" ^ V.pp d ^ ") = " ^ V.pp r' ^ "\n")
    in ()
    end

fun try_fun {name, f, arg, d} =
    let val () = print ("\nTrying fun example: " ^ name ^ "\n")
        val () = print ("  f = " ^ F.pp f ^ "\n")
        val (r,l) = D.diff f arg
        val () = print ("  f(" ^ V.pp arg ^ ") = " ^ V.pp r ^ "\n")
        val () = print ("  f'(" ^ V.pp arg ^ ") = " ^ L.pp l ^ "\n")
        val r' = L.eval l d
        val () = print ("  f'(...)(" ^ V.pp d ^ ") = " ^ V.pp r' ^ "\n")
    in ()
    end

local open E.DSL
in
val () = try_ex {name="ex1", e=ln (sin x1), arg=V.T[V.R 3.0], d=V.T[V.R 1.0]}
val () = try_ex {name="ex2", e=x1*x2, arg=V.T[V.R 3.0,V.R 1.0], d=V.T[V.R 1.0,V.R 0.0]}
val () = try_ex {name="ex3", e=ln x1 + x1*x2 - sin x2, arg=V.T[V.R 3.0,V.R 1.0], d=V.T[V.R 1.0,V.R 0.0]}
end

local open F.DSL
      infix x nonfix + nonfix *
in
val () = try_fun {name="fun1", f=(id x ln) o dup o (+) o (cos x sin),arg=V.T[V.R 1.5,V.R 2.0],d=V.T[V.R 2.0,V.R 2.0]}
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
        val r' = L.eval l d
        val () = print ("  f'(" ^ V.pp arg ^ ")(" ^ V.pp d ^ ") = " ^ V.pp r' ^ "\n")
        val () = print ("  f'_simpl(" ^ V.pp arg ^ ")(" ^ V.pp d ^ ") = " ^ V.pp (V.simpl r') ^ "\n")
    in ()
    end

local open E.DSL
in
val () = try_ex {name="t1", e=ln (sin x1), arg=V.T[V.Var "x1"], d=V.T[V.R 1.0]}
val () = try_ex {name="t2", e=x1*x2, arg=V.T[V.Var "x1",V.Var "x2"], d=V.T[V.R 1.0,V.R 0.0]}
val () = try_ex {name="t3", e=ln x1 + x1*x2 - sin x2, arg=V.T[V.Var "x1",V.Var "x2"], d=V.T[V.R 1.0,V.R 0.0]}
end

end
