(* Dynamically tagged version of combinatory differentiation interpretation (in SML)
 *
 * Todo:
 *  1) Evaluate Lin expressions
 *  2) Experiment with forward/reverse mode differences
 *  3) Instead of evaluating expressions, I believe we can build up
 *     expressions parameterised over the input variables (at least when
 *     we don't try to differentiate conditional expressions, recursion,
 *     and such...
 *  4) Optimisations at the Fun level: convert `(pi1 x pi2) o dup` into `id`
 *
 * Questions:
 *  1) Can we somehow convert point-free notation to expressions with let-expressions?
 *)

fun die s = (print ("Error: " ^ s ^ "\n"); raise Fail s)

datatype ty = REAL | INT | PROD of ty list | ARROW of ty*ty | LIST of ty
datatype v = R of real | I of int | A of (v->v) * ty | L of v list * ty | T of v list

fun pp_ty ty =
    case ty of
        REAL => "REAL"
      | INT => "INT"
      | PROD tys => "(" ^ String.concatWith "," (map pp_ty tys) ^ ")"
      | ARROW(ty1,ty2) => "(" ^ pp_ty ty1 ^ "->" ^ pp_ty ty2 ^ ")"
      | LIST ty => "[" ^ pp_ty ty ^ "]"
fun pp_v v =
    case v of
        R r => Real.toString r
      | I i => Int.toString i
      | T vs => "(" ^ String.concatWith "," (map pp_v vs) ^ ")"
      | A _ => "func"
      | L _ => "list"

fun lift2 c dc f : v*v->v =
    fn (a,b) => c(f(dc a, dc b))
fun lift1 c dc f : v -> v =
    fn a => c(f(dc a))

val lift2R : (real*real->real) -> (v*v->v) =
    lift2 R (fn R r => r | v => die ("type error - expecting real - 2R - got " ^ pp_v v))
val lift1R : (real->real) -> (v->v) =
    lift1 R (fn R r => r | v => die ("type error - expecting real - 1R - got " ^ pp_v v))

val lift2I : (int*int->int) -> (v*v->v) =
    lift2 I (fn I i => i | _ => die "type error - expecting int")
val lift1I : (int->int) -> (v->v) =
    lift1 I (fn I i => i | _ => die "type error - expecting int")

fun liftP s (f: v*v->v) : v -> v =
    fn T [x1,x2] => f (x1,x2)
     | v => die ("type error liftP - expecting pair (" ^ s ^ ") - got " ^ pp_v v)

fun prjI s i =
    fn T xs => (List.nth(xs,i-1) handle _ => die (s ^ " index error"))
     | v => die ("type error prjI - expecting tuple (" ^ s ^ ") - got " ^ pp_v v)

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
       | K of v            (* X -> Y *)
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
      | K v => pp_v v
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
end

signature LIN = sig
  type bin = string * (v * v -> v)
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

structure Lin :> LIN = struct
type bin = string * (v * v -> v)
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
      | CurryL(("add",_),v) => "(" ^ pp_v v ^ "+)"
      | CurryL(("mul",_),v) => "(" ^ pp_v v ^ "*)"
      | CurryL((s,_),v) => "(" ^ pp_v v ^ " " ^ s ^ ")"
      | CurryR(("add",_),v) => "(+" ^ pp_v v ^ ")"
      | CurryR(("mul",_),v) => "(*" ^ pp_v v ^ ")"
      | CurryR((s,_),v) => "(" ^ s ^ " " ^ pp_v v ^ ")"

fun eval (e:lin) (x:v) : v =
    case e of
        Zero => R 0.0
      | Id => x
      | Lin(s,f) => (f x handle X => (print ("Lin problem: " ^ s ^ "; x=" ^ pp_v x ^ "\n"); raise X))
      | Prj i =>
        (case x of
             T xs => (List.nth(xs,i-1) handle _ => die "eval.index error")
           | v => die ("eval.expecting tuple - got " ^ pp_v v))
      | Oplus(f,g) =>
        (case x of
             T[x,y] => T[eval f x,eval g y]
           | v => die ("eval.Oplus: expecting pair - got " ^ pp_v v))
      | Comp(g,f) => eval g (eval f x)
      | CurryL((s,f),v) => (f(v,x) handle X => (print ("CurryL problem: " ^ s ^ "; v=" ^
                                                       pp_v v ^ "; x=" ^ pp_v x ^ "\n"); raise X))
      | CurryR((s,f),v) => (f(x,v) handle X => (print ("CurryR problem: " ^ s ^ "; x=" ^
                                                       pp_v x ^ "; v=" ^ pp_v v ^ "\n"); raise X))

val mulR : bin = ("mul", lift2R (op * ))
end

structure Diff = struct
structure L = Lin
structure F = Fun
fun diff (f:F.f) (x:v) : v * L.lin =
    case f of
        F.Comp(g,f) =>
        let val (fx,f'x) = diff f x
            val (gfx,g'fx) = diff g fx
        in (gfx,L.comp(g'fx,f'x))
        end
      | F.K y => (y, L.zero)
      | F.Add =>
        let val h = liftP "add" (lift2R (op +))
        in (h x, L.lin("add",h))
        end
      | F.Cos => (lift1R Math.cos x,
                  L.curryL (L.mulR,lift1R Math.sin x))
      | F.Sin => (lift1R Math.sin x,
                  L.curryL (L.mulR,lift1R (~ o Math.cos) x))
      | F.Ln => (lift1R Math.ln x,
                 L.curryL (L.mulR,lift1R (fn y => 1.0/y) x))
      | F.Exp => (lift1R Math.exp x,
                  L.curryL (L.mulR,lift1R Math.exp x))
      | F.Pow i => (lift1R (fn a => Math.pow(a,real i)) x,
                    L.curryL (L.mulR,lift1R (fn a => real i * Math.pow(a,real(i-1))) x))
      | F.Neg => (lift1R Real.~ x,
                  L.curryL (L.mulR,lift1R Real.~ x))
      | F.Prj i =>
        let val h = prjI ("Prj" ^ Int.toString i) i
        in (h x, L.prj i)
        end
      | F.Dup =>
        let val h = fn v => T[v,v]
        in (h x, L.lin("dup",h))
        end
      | F.FProd(f,g) =>
        (case x of
             T[x,y] =>
             let val (fx,f'x) = diff f x
                 val (gy,g'y) = diff g y
             in (T[fx,gy],L.oplus(f'x,g'y))
             end
           | _ => die "type error - fpair expects pair")
      | F.Mul =>
        (case x of
             T[x,y] =>
             let val h = ("mul",lift2R (op * ))
             in (lift2R (op * ) (x,y),
                 L.comp(L.lin ("add",liftP "mul-case" (lift2R (op+))),
                        L.oplus(L.curryR(h,y),
                                L.curryL(h,x))))
             end
           | _ => die "type error - multiplication expects pair")
      | F.Id => (x, L.id)
end

structure Exp = struct
structure F = Fun
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
      | C v => pp_v v
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
      | X _ => die "supports currently only 2 variables X(1) and X(2)"
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
fun try_ex {name, e, arg, d} =
    let val () = print ("Trying example: " ^ name ^ "\n")
        val () = print ("  e = " ^ Exp.pp e ^ "\n")
        val f1 = Exp.trans e
        val () = print ("  f_unopt = " ^ Fun.pp f1 ^ "\n")
        val f = Fun.opt f1
        val () = print ("  f = " ^ Fun.pp f ^ "\n")
        val (r,l) = Diff.diff f arg
        val () = print ("  f(" ^ pp_v arg ^ ") = " ^ pp_v r ^ "\n")
        val () = print ("  f'(" ^ pp_v arg ^ ") = " ^ Lin.pp l ^ "\n")
        val r' = Lin.eval l d
        val () = print ("  f'(...)(" ^ pp_v d ^ ") = " ^ pp_v r' ^ "\n")
    in ()
    end
local open Exp.DSL
in
val () = try_ex {name="ex1", e=ln (sin x1), arg=T[R 3.0], d=T[R 1.0]}
val () = try_ex {name="ex2", e=x1*x2, arg=T[R 3.0,R 1.0], d=T[R 1.0,R 0.0]}
val () = try_ex {name="ex3", e=ln x1 + x1*x2 - sin x2, arg=T[R 3.0,R 1.0], d=T[R 1.0,R 0.0]}
end
end
