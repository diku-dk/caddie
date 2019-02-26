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

structure Vec = struct
  type vs = {vty:ty,fty:ty,add:v*v->v,scale:v*v->v,zero:v,one:v,neg:v->v,inv:v->v}

  val vs_real : vs =
      {vty   = REAL,
       fty   = REAL,
       add   = lift2R Real.+,
       scale = lift2R Real.*,
       zero  = R 0.0,
       one   = R 1.0,
       neg   = lift1R (Real.~),
       inv   = lift1R (fn x => Real./(1.0,x))}

  val vs_int : vs =
      {vty   = INT,
       fty   = INT,
       add   = lift2I Int.+,
       scale = lift2I Int.*,
       zero  = I 0,
       one   = I 1,
       neg   = lift1I (Int.~),
       inv   = lift1I (fn x => Int.div(1,x))}

  fun prod_vs ({vty,fty,add,scale,zero,one,neg,inv}:vs) : vs =
      {vty=PROD(vty,vty),fty=PROD(fty,fty),
       add=fn (P(x1,y1),P(x2,y2)) => P(add(x1,x2),add(y1,y2))
            | _ => die "type error",
       scale=fn (P(x1,y1),P(x2,y2)) => P(scale(x1,x2),scale(y1,y2))
              | _ => die "type error",
       zero=P(zero,zero),
       one=P(one,one),
       neg=fn P(x,y) => P(neg x,neg y)
            | _ => die "type error",
       inv=fn P(x,y) => P(inv x,inv y)
            | _ => die "type error"}
end

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

(*
fun dom f =
    case f of
        Ln => REAL
      | Exp => REAL
      | Sin => REAL
      | Cos => REAL
      | Pow _ => REAL
      | Comp(f,g) => dom g
      | Add => PROD(REAL,REAL)
      | Mul => PROD(REAL,REAL)
      | K(_,t) => t
      | Prj1 t => t
      | Prj2 t => t
      | FPair(f,g) => PROD(dom f,dom g)

fun ran f =
    case f of
        Ln => REAL
      | Exp => REAL
      | Sin => REAL
      | Cos => REAL
      | Pow _ => REAL
      | Comp(f,g) => ran f
      | Add => REAL
      | Mul => REAL
      | K(v,_) => ty_of_v v
      | Prj1 (PROD(t,_)) => t
      | Prj2 (PROD(_,t)) => t
      | Prj1 _ => die "type error - expecting prod"
      | Prj2 _ => die "type error - expecting prod"
      | FPair(f,g) => PROD(ran f,ran g)
*)
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
val mulR : bin = lift2R (op *)
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
