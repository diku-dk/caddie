fun die s = (print ("Error (Lin): " ^ s ^ "\n"); raise Fail s)

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

val add = lin("add",V.add)
val dup = lin("dup",fn v => V.T[v,v])
val neg = lin("neg",V.uprim Prim.Neg)

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
val letBind = V.letBind

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


end
