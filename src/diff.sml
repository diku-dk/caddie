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
  datatype v = R of real | I of int | T of v list
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

structure Fun = struct

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
       | K of Val.v        (* X -> Y *)
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
      | K v => Val.pp v
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
end (* Fun *)

signature LIN = sig
  type v
  type bin = string * (v -> v)
  type lin

  (* Constructors *)
  val lin    : string * (v -> v) -> lin
  val prj    : int -> lin
  val zero   : lin
  val id     : lin
  val oplus  : lin * lin -> lin
  val comp   : lin * lin -> lin
  val curryL : bin * v -> lin
  val curryR : bin * v -> lin

  val mulR   : bin

  val pp     : lin -> string
  val eval   : lin -> v -> v
end

structure Lin :> LIN where type v = Val.v = struct
type v = Val.v
type bin = string * (v -> v)
datatype lin = Lin of string * (v -> v)
             | Prj of int
             | Zero
             | Id
             | Oplus of lin * lin
             | Comp of lin * lin
             | CurryL of bin * v
             | CurryR of bin * v

val lin = Lin
val prj = Prj
val zero = Zero
val id = Id
val oplus = Oplus
val comp = Comp
val curryL = CurryL
val curryR = CurryR

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
      | CurryL(("add",_),v) => "(" ^ Val.pp v ^ "+)"
      | CurryL(("mul",_),v) => "(" ^ Val.pp v ^ "*)"
      | CurryL((s,_),v) => "(" ^ Val.pp v ^ " " ^ s ^ ")"
      | CurryR(("add",_),v) => "(+" ^ Val.pp v ^ ")"
      | CurryR(("mul",_),v) => "(*" ^ Val.pp v ^ ")"
      | CurryR((s,_),v) => "(" ^ s ^ " " ^ Val.pp v ^ ")"

fun eval (e:lin) (x:v) : v =
    case e of
        Zero => Val.R 0.0
      | Id => x
      | Lin(s,f) => (f x handle X => (print ("Lin problem: " ^ s ^ "; x=" ^ Val.pp x ^ "\n"); raise X))
      | Prj i => Val.prjI "eval projection error" i x
      | Oplus(f,g) =>
        (case x of
             Val.T[x,y] => Val.T[eval f x,eval g y]
           | v => die ("eval.Oplus: expecting pair - got " ^ Val.pp v))
      | Comp(g,f) => eval g (eval f x)
      | CurryL((s,f),v) => (f(Val.T[v,x]) handle X => (print ("CurryL problem: " ^ s ^ "; v=" ^
                                                              Val.pp v ^ "; x=" ^ Val.pp x ^ "\n"); raise X))
      | CurryR((s,f),v) => (f(Val.T[x,v]) handle X => (print ("CurryR problem: " ^ s ^ "; x=" ^
                                                              Val.pp x ^ "; v=" ^ Val.pp v ^ "\n"); raise X))

val mulR : bin = ("mul", Val.mul)
end

structure Diff = struct
structure L = Lin
structure F = Fun
structure V = Val
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
                  L.curryL (L.mulR,V.sin x))
      | F.Sin => (V.sin x,
                  L.curryL (L.mulR,V.neg (V.cos x)))
      | F.Ln => (V.ln x,
                 L.curryL (L.mulR,V.pow (~1) x))
      | F.Exp => (V.exp x,
                  L.curryL (L.mulR,V.exp x))
      | F.Pow i => (V.pow i x,
                    L.curryL (L.mulR,V.mul(V.T[V.R (real i),V.pow (i-1) x])))
      | F.Neg => (V.neg x,
                  L.curryL (L.mulR,V.neg x))
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
                L.oplus(L.curryR(L.mulR,V.prjI "mul-R" 2 x),
                        L.curryL(L.mulR,V.prjI "mul-L" 1 x))))
      | F.Id => (x, L.id)
end

structure Exp = struct
structure F = Fun
structure V = Val
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
      | C v => Val.pp v
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

structure Ex = struct
structure V = Val
fun try_ex {name, e, arg, d} =
    let val () = print ("Trying example: " ^ name ^ "\n")
        val () = print ("  e = " ^ Exp.pp e ^ "\n")
        val f1 = Exp.trans e
        val () = print ("  f_unopt = " ^ Fun.pp f1 ^ "\n")
        val f = Fun.opt f1
        val () = print ("  f = " ^ Fun.pp f ^ "\n")
        val (r,l) = Diff.diff f arg
        val () = print ("  f(" ^ Val.pp arg ^ ") = " ^ Val.pp r ^ "\n")
        val () = print ("  f'(" ^ Val.pp arg ^ ") = " ^ Lin.pp l ^ "\n")
        val r' = Lin.eval l d
        val () = print ("  f'(...)(" ^ Val.pp d ^ ") = " ^ Val.pp r' ^ "\n")
    in ()
    end
local open Exp.DSL
in
val () = try_ex {name="ex1", e=ln (sin x1), arg=V.T[V.R 3.0], d=V.T[V.R 1.0]}
val () = try_ex {name="ex2", e=x1*x2, arg=V.T[V.R 3.0,V.R 1.0], d=V.T[V.R 1.0,V.R 0.0]}
val () = try_ex {name="ex3", e=ln x1 + x1*x2 - sin x2, arg=V.T[V.R 3.0,V.R 1.0], d=V.T[V.R 1.0,V.R 0.0]}
end
end
