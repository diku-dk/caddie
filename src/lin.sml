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

val ret = V.ret
infix >>=
val op >>= = V.>>=
val letBind = ret (*V.letBind*)

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

fun transp (e:lin) : lin =
    case e of
        Zero => Zero
      | Id => Id
      | Comp(g,f) => Comp(transp f,transp g)
      | Oplus(f,g) => Oplus(transp f,transp g)
      | Lin("dup",_) => add
      | Lin("add",_) => dup
      | Lin("neg",_) => e
      | Lin(s,f) => die ("transpose of linear function not supported: "
                         ^ s)
      | Prj (2,1) => Comp(Oplus(Id,Zero),dup)
      | Prj (2,2) => Comp(Oplus(Zero,Id),dup)
      | Prj (d,i) => die ("transpose of projection not supported: "
                          ^ Int.toString i ^ "/" ^ Int.toString d)
      | CurL(Prim.Mul,v) => e
      | CurR(Prim.Mul,v) => e
      | CurL(Prim.Dprod,v) => CurR(Prim.Mul,v)
      | CurR(Prim.Dprod,v) => CurR(Prim.Mul,v)
      | CurL(Prim.Sprod,v) => e
      | CurR(Prim.Sprod,v) => CurR(Prim.Dprod,v)
      | CurL(p,v) =>
        die ("transp.CurL problem: " ^
             Prim.pp_bilin p ^ "; v=" ^ V.pp v)
      | CurR(p,v) =>
        die ("transp.CurR problem: " ^
             Prim.pp_bilin p ^ "; v=" ^ V.pp v)

end
