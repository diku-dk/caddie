(* Dynamically tagged version of combinatory differentiation interpretation (in SML)
 *
 * There are currently a number of issues with the code. First, for
 * functions that take only one argument, we need to treat Prj1 as the
 * identity.. Second, differentiation of
 *
 * Todo:
 *  1) Fix issues
 *  2) Pretty-print/evaluate Lin expressions
 *  3) Experiment with forward/reverse mode differences
 *  4) Instead of evaluating expressions, I believe we can build up
 *     expressions parameterised over the input variables (at least when
 *     we don't try to differentiate conditional expressions, recursion,
 *     and such...
 *)

fun die s = (print ("Error: " ^ s ^ "\n"); raise Fail s)

datatype ty = REAL | INT | PROD of ty * ty | ARROW of ty*ty | LIST of ty
datatype v = R of real | I of int | P of v * v | A of (v->v) * ty | L of v list * ty

fun pp_ty ty =
    case ty of
        REAL => "REAL"
      | INT => "INT"
      | PROD(ty1,ty2) => "(" ^ pp_ty ty1 ^ "," ^ pp_ty ty2 ^ ")"
      | ARROW(ty1,ty2) => "(" ^ pp_ty ty1 ^ "->" ^ pp_ty ty2 ^ ")"
      | LIST ty => "[" ^ pp_ty ty ^ "]"
fun pp_v v =
    case v of
        R r => Real.toString r
      | I i => Int.toString i
      | P(v1,v2) => "(" ^ pp_v v1 ^ "," ^ pp_v v2 ^ ")"
      | A _ => "func"
      | L _ => "list"

fun ty_of_v v =
    case v of
        R _ => REAL
      | I _ => INT
      | P(a,b) => PROD(ty_of_v a,ty_of_v b)
      | A(_,ty) => ty
      | L(_,ty) => ty

fun lift2 c dc f : v*v->v =
    fn (a,b) => c(f(dc a, dc b))
fun lift1 c dc f : v -> v =
    fn a => c(f(dc a))

val lift2R : (real*real->real) -> (v*v->v) =
    lift2 R (fn R r => r | _ => die "type error - expecting real")
val lift1R : (real->real) -> (v->v) =
    lift1 R (fn R r => r | _ => die "type error - expecting real")

val lift2I : (int*int->int) -> (v*v->v) =
    lift2 I (fn I i => i | _ => die "type error - expecting int")
val lift1I : (int->int) -> (v->v) =
    lift1 I (fn I i => i | _ => die "type error - expecting int")

fun liftP s (f: v*v->v) : v -> v =
    fn P p => f p
     | _ => die ("type error liftP - expecting pair (" ^ s ^ ")")

structure Fun = struct

datatype f =
         Comp of f * f     (* X -> Y *)
       | Ln                (* R -> R *)
       | Exp               (* R -> R *)
       | Sin               (* R -> R *)
       | Cos               (* R -> R *)
       | Pow of int        (* R -> R *)
       | Neg               (* R -> R *)
       | Prj1              (* X*Y->X *)
       | Prj2              (* X*Y->Y *)
       | Add               (* R*R->R *)
       | Mul               (* R*R->R *)
       | K of v
       | FProd of f * f
       | Dup

fun pp e =
    case e of
        Comp(f,g) => pp f ^ " o " ^ pp g
      | Ln => "ln"
      | Exp => "exp"
      | Sin => "sin"
      | Cos => "cos"
      | Pow i => "pow(" ^ Int.toString i ^ ")"
      | Neg => "~"
      | Prj1 => "pi1"
      | Prj2 => "pi2"
      | Add => "(+)"
      | Mul => "(*)"
      | K v => pp_v v
      | FProd(f,g) => "(" ^ pp f ^ " x " ^ pp g ^ ")"
      | Dub => "dup"
end

structure Lin = struct
type bin = v * v -> v
datatype lin = Lin of v -> v
             | Zero
             | Id
             | Oplus of lin * lin
             | Comp of lin * lin
             | CurryL of bin * v
             | CurryR of bin * v
val mulR : bin = lift2R (op * )
end

structure Diff = struct
structure L = Lin
structure F = Fun
fun println s = print (s ^ "\n")
fun diff (f:F.f) (x:v) : v * L.lin =
    case f of
        F.Comp(f,g) =>
        let val () = println "comp"
            val (fx,f'x) = diff f x
            val (gfx,g'fx) = diff g fx
        in (fx,L.Comp(g'fx,f'x))
        end
      | F.K y => (y, L.Zero) before println "k"
      | F.Add =>
        let val () = println "add"
            val h = liftP "add" (lift2R (op +))
        in (h x, L.Lin h)
        end
      | F.Cos => (println "cos"; (lift1R Math.cos x,
                                  L.CurryL (L.mulR,lift1R Math.sin x)))
      | F.Sin => (println "sin"; (lift1R Math.sin x,
                                  L.CurryL (L.mulR,lift1R (~ o Math.cos) x)))
      | F.Ln => (println "ln"; (lift1R Math.ln x,
                                L.CurryL (L.mulR,lift1R (fn y => 1.0/y) x)))
      | F.Exp => (println "exp"; (lift1R Math.exp x,
                                  L.CurryL (L.mulR,lift1R Math.exp x)))
      | F.Pow i => (println "pow"; (lift1R (fn a => Math.pow(a,real i)) x,
                                    L.CurryL (L.mulR,lift1R (fn a => real i * Math.pow(a,real(i-1))) x)))
      | F.Neg => (println "neg"; (lift1R Real.~ x,
                                  L.CurryL (L.mulR,lift1R Real.~ x)))
      | F.Prj1 =>
        let val () = println "prj1"
            val h = liftP "prj1" (#1)
        in (h x, L.Lin h)
        end
      | F.Prj2 =>
        let val () = println "prj2"
            val h = liftP "prj2" (#2)
        in (h x, L.Lin h)
        end
      | F.Dup =>
        let val () = println "dup"
            val h = fn v => P(v,v)
        in (h x, L.Lin h)
        end
      | F.FProd(f,g) =>
        (case x of
             P(x,y) =>
             let val () = println "fpair"
                 val (fx,f'x) = diff f x
                 val (gy,g'y) = diff g y
             in (P(fx,gy),L.Oplus(f'x,g'y))
             end
           | _ => die "type error - fpair expects pair")
      | F.Mul =>
        (case x of
             P(x,y) =>
             let val () = println "mul"
                 val h = lift2R (op * )
             in (lift2R (op * ) (x,y),
                 L.Comp(L.Lin (liftP "mul" (lift2R (op+))),
                        L.Oplus(L.CurryR(h,y),
                                L.CurryL(h,x))))
             end
           | _ => die "type error - multiplication expects pair")
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

fun lrangle (f,g) = F.Comp(F.FProd(f,g),F.Dup)
fun hat opr (f,g) = F.Comp(opr,lrangle(f,g))

fun trans e =
    case e of
        X 1 => F.Prj1
      | X 2 => F.Prj2
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

structure Ex = struct
local open Exp.DSL
in
  val ex1_ = ln(sin x1)
  val ex2_ = ln x1 + x1*x2 - sin x2
end
val ex1 = Exp.trans ex1_
val ex2 = Exp.trans ex2_

fun pr_e s e = print (s ^ " = " ^ Fun.pp e ^ "\n")
val () = pr_e "ex1" ex1
val () = pr_e "ex2" ex2
val ex1' = Diff.diff ex2 (P(R 3.0,R 1.0))
end
