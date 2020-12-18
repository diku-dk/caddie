fun die s = (print ("Error (Val): " ^ s ^ "\n"); raise Fail s)

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
        Prim.Sin => lift1R Math.cos
      | Prim.Cos => lift1R (~ o Math.sin)
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

fun iff (v,m1,m2) =
    case v of
        R v => if v >= 0.0 then m1 else m2
      | _ => die "iff: expecting real"

fun ppM (ind:string) (pp:'a -> string) (x: 'a M) : string = ind ^ pp x

val getVal = fn x => x
end

fun eq (R r, R r') = Real.abs(r - r') < 0.0000000001
  | eq (T vs,T vs') = (List.all eq (ListPair.zip(vs,vs'))
                       handle _ => false)
  | eq _ = false
end
