fun die s = (print ("Error (Lin): " ^ s ^ "\n"); raise Fail s)

functor Lin(V:VAL) :> LIN where type v = V.v and type 'a M = 'a V.M and type 'a f = 'a V.f = struct
type v = V.v
type 'a f = 'a V.f
type 'a M = 'a V.M

datatype lin = Lin of string * (v -> v)
             | Add of int
             | Dup of int
             | Prj of int * int           (* (dim, idx) *)
             | Zero
             | Id
             | Oplus of lin list
             | Comp of lin * lin
             | CurL of Prim.bilin * v
             | CurR of Prim.bilin * v
             | If of v * lin M * lin M
             | LMap of lin
             | Zip of lin list
             | LMapP of lin f M * v
             | Red of Rel.r

val lin = Lin
fun prj d i = Prj (d,i)
val zero = Zero
val id = Id
val oplus = Oplus
val comp = Comp
val curL = CurL
val curR = CurR
val lmap = LMap
val zip = Zip
val lmapP = LMapP
val red = Red

val add = Add
val dup = Dup
val neg = lin("neg",V.uprim Prim.Neg)

fun pp e =
    case e of
        Add 2 => "(+)"
      | Add n => "add" ^ Int.toString n
      | Dup 2 => "dup"
      | Dup n => "dup" ^ Int.toString n
      | Lin(s,_) => s
      | Prj (d,i) => "pi_" ^ Int.toString i ^ "/" ^ Int.toString d
      | Zero => "zero"
      | Id => "id"
      | Oplus[e1,e2] => "(" ^ pp e1 ^ " :+: " ^ pp e2 ^ ")"
      | Oplus es => "oplus(" ^ String.concatWith "," (map pp es) ^ ")"
      | Comp(e1,e2) => pp e1 ^ " :o: " ^ pp e2
      | CurL(p,v) => "(" ^ V.pp v ^ " " ^ Prim.pp_bilin p ^ ")"
      | CurR(p,v) => "(" ^ Prim.pp_bilin p ^ " " ^ V.pp v ^ ")"
      | If(v,m1,m2) => "(if " ^ V.pp v ^ " then " ^ V.ppM "  " pp m1 ^ " else " ^ V.ppM "  " pp m2 ^ ")"

      | LMap f => "(lmap (" ^ pp f ^ "))"
      | Zip fs => "(zip (" ^ String.concatWith "," (map pp fs) ^ "))"
      | LMapP (f, vs) => "(lmapP (" ^ V.ppM "   " (V.pp_f pp) f ^ "," ^ V.pp vs ^ "))"
      | Red r => "red(" ^ Rel.pp r ^ ")"

val ret = V.ret
infix >>=
val op >>= = V.>>=
val letBind = ret (*V.letBind*)
val iff = If

fun eval (e:lin) (x:v) : v V.M =
    case e of
        Zero => ret V.Z
      | Id => ret x
      | Dup n => V.letBind x >>= (fn v => ret(V.T(List.tabulate(n,fn _ => v))))
      | Add 2 => ret (V.add x)
      | Add 3 => ret (V.add (V.T[V.add (V.T[V.prjI "Add3.1" 1 x,
                                            V.prjI "Add3.2" 2 x]),
                                 V.prjI "Add3.3" 3 x]))
      | Add n => die ("eval.Add(" ^ Int.toString n ^ ") not supported")
      | Lin(s,f) => (letBind (f x) handle X => (print ("Lin problem: " ^ s ^ "; x=" ^ V.pp x ^ "\n"); raise X))
      | Prj (d,i) => ret (V.prjI ("eval projection error (" ^ Int.toString d ^ ")") i x)
      | Oplus fs =>
        (case V.unT x of
             SOME xs =>
             evals fs xs >>= (fn vs =>
             letBind (V.T vs))
           | NONE =>
             letBind x >>= (fn v =>
             evals fs (List.tabulate(length fs, fn i => V.prjI "Oplus" (i+1) v)) >>= (fn vs =>
             letBind (V.T vs))))
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
      | LMap f => ret(V.mapM (eval f) x)
      | Zip fs  => V.zipM (map eval fs) x
      | LMapP (f, vs)  =>
         ret (V.mapP f (fn l => ret(V.mapM (eval l) x)) vs)
      | Red r => ret (V.red r x)

and evals fs xs =
    case (fs,xs) of
        (nil,nil) => ret nil
      | (f::fs,x::xs) =>
        eval f x >>= (fn v =>
        evals fs xs >>= (fn vs => ret (v::vs)))
      | _ => die "eval.oplus.different number of functions and parameters"

fun adjoint (e:lin) : lin =
    case e of
        Zero => Zero
      | Id => Id
      | Comp(g,f) => Comp(adjoint f,adjoint g)
      | Oplus fs => Oplus(map adjoint fs)
      | Add n => Dup n
      | Dup n => Add n
      | Lin("neg",_) => e
      | Lin(s,f) => die ("adjoint of linear function not supported: "
                         ^ s ^ " - maybe you need to add a case")
      | Prj (n,i) => Comp(Oplus(List.tabulate(n,fn j => if j+1=i then Id else Zero)), dup n)
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
      | LMap f => LMap (adjoint f)
      | Zip fs  => Zip (map adjoint fs)
      | LMapP (f, vs) => LMapP (V.fmap (V.fmap_f adjoint) f, vs)  (* fix *)
      | Red r => Red (Rel.trans r)

end
