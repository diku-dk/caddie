fun die s = (print ("Error (Lin): " ^ s ^ "\n"); raise Fail s)

functor Lin(V:VAL) :> LIN where type v = V.v and type 'a M = 'a V.M = struct
type v = V.v
type 'a M = 'a V.M

datatype lin = Lin of string * (v -> v)
             | Prj of int * int           (* (dim, idx) *)
             | Zero
             | Id
             | Oplus of lin * lin
             | Comp of lin * lin
             | CurL of Prim.bilin * v
             | CurR of Prim.bilin * v
             | If of v * lin M * lin M

val lin = Lin
fun prj d i = Prj (d,i)
val zero = Zero
val id = Id
val oplus = Oplus
val comp = Comp
val curL = CurL
val curR = CurR

val add = lin("add",V.add)
val dup = lin("dup",fn v => V.T[v,v])
val neg = lin("neg",V.uprim Prim.Neg)

fun pp e =
    case e of
        Lin("add",_) => "(+)"
      | Lin(s,_) => s
      | Prj (d,i) => "pi_" ^ Int.toString i ^ "/" ^ Int.toString d
      | Zero => "zero"
      | Id => "id"
      | Oplus(e1,e2) => "(" ^ pp e1 ^ " :+: " ^ pp e2 ^ ")"
      | Comp(e1,e2) => pp e1 ^ " :o: " ^ pp e2
      | CurL(p,v) => "(" ^ V.pp v ^ " " ^ Prim.pp_bilin p ^ ")"
      | CurR(p,v) => "(" ^ Prim.pp_bilin p ^ " " ^ V.pp v ^ ")"
      | If(v,m1,m2) => "(if " ^ V.pp v ^ " then " ^ V.ppM "  " pp m1 ^ " else " ^ V.ppM "  " pp m2 ^ ")"

val ret = V.ret
infix >>=
val op >>= = V.>>=
val letBind = ret (*V.letBind*)
val iff = If

fun eval (e:lin) (x:v) : v V.M =
    case e of
        Zero => ret (V.R 0.0)
      | Id => ret x
      | Lin("dup",f) => V.letBind x >>= (ret o f)
      | Lin(s,f) => (letBind (f x) handle X => (print ("Lin problem: " ^ s ^ "; x=" ^ V.pp x ^ "\n"); raise X))
      | Prj (d,i) => ret (V.prjI ("eval projection error (" ^ Int.toString d ^ ")") i x)
      | Oplus(f,g) =>
        (case V.unT x of
             SOME [x,y] => eval f x >>= (fn v1 =>
                           eval g y >>= (fn v2 =>
                           letBind (V.T[v1,v2])))
           | _ => die ("eval.Oplus: expecting pair - got " ^ V.pp x))
      | Comp(g,f) => eval f x >>= eval g
      | CurL(p,v) => letBind (V.bilin (p,V.T[v,x])
                              handle X => (print ("CurL problem: " ^
                                                  Prim.pp_bilin p ^ "; v=" ^
                                                  V.pp v ^ "; x=" ^ V.pp x ^ "\n");
                                           raise X))
      | CurR(p,v) => letBind (V.bilin (p,V.T[x,v])
                              handle X => (print ("CurR problem: " ^
                                                  Prim.pp_bilin p ^ "; x=" ^
                                                  V.pp x ^ "; v=" ^ V.pp v ^ "\n");
                                           raise X))
      | If(v,m1,m2) => ret(V.iff (v,
                                  m1 >>= (fn m1 => eval m1 x),
                                  m2 >>= (fn m2 => eval m2 x)))

fun adjoint (e:lin) : lin =
    case e of
        Zero => Zero
      | Id => Id
      | Comp(g,f) => Comp(adjoint f,adjoint g)
      | Oplus(f,g) => Oplus(adjoint f,adjoint g)
      | Lin("dup",_) => add
      | Lin("add",_) => dup
      | Lin("neg",_) => e
      | Lin(s,f) => die ("adjoint of linear function not supported: "
                         ^ s ^ " - maybe you need to add a case")
      | Prj (2,1) => Comp(Oplus(Id,Zero),dup)
      | Prj (2,2) => Comp(Oplus(Zero,Id),dup)
      | Prj (d,i) => die ("adjoint of projection not supported: "
                          ^ Int.toString i ^ "/" ^ Int.toString d)
      | CurL(Prim.Mul,v) => e
      | CurR(Prim.Mul,v) => e
      | CurL(Prim.Dprod,v) => CurR(Prim.Mul,v)
      | CurR(Prim.Dprod,v) => CurR(Prim.Mul,v)
      | CurL(Prim.Sprod,v) => e
      | CurR(Prim.Sprod,v) => CurR(Prim.Dprod,v)
      | CurL(p,v) =>
        die ("adjoint.CurL problem: " ^
             Prim.pp_bilin p ^ "; v=" ^ V.pp v)
      | CurR(p,v) =>
        die ("adjoint.CurR problem: " ^
             Prim.pp_bilin p ^ "; v=" ^ V.pp v)
      | If(v,m1,m2) => If(v,
                          m1 >>= (ret o adjoint),
                          m2 >>= (ret o adjoint))

end
