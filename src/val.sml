fun die s = (print ("Error (Val): " ^ s ^ "\n"); raise Fail s)

structure Val :> VAL = struct

datatype v = R of real | T of v list | Z


val VarOpt = NONE
fun unT (T xs) = SOME xs
  | unT _ = NONE

fun unR (R v) = SOME v
  | unR _ = NONE

fun isZ Z = true
  | isZ _ = false

fun real_to_string r =
    let val s = CharVector.map (fn #"~" => #"-" | c => c) (Real.toString r)
    in if size s >= 2
          andalso String.sub(s,size s - 1) = #"0"
          andalso String.sub(s,size s - 2) = #"."
       then String.extract (s,0,SOME(size s - 2))
       else s
    end

fun pp v =
    case v of
        R r => real_to_string r
      | T vs => "(" ^ String.concatWith "," (map pp vs) ^ ")"
      | Z => "Z"

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


val add =
    let fun add (Z,v2) = v2
          | add (v1,Z) = v1
          | add (R r1,R r2) = R (r1+r2)
          | add (T vs1, T vs2) =
            (T (ListPair.mapEq add (vs1,vs2))
             handle _ => die "add expects equally length tuples")
          | add _ = die "add expects arguments of the same type"
    in liftP "add" add
    end

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

fun fmap f ma = f ma

fun sequence mas = mas

fun ppM (ind:string) (pp:'a -> string) (x: 'a M) : string = ind ^ pp x

val getVal = fn x => x
end

fun eq (R r, R r') = Real.abs(r - r') < 0.0000000001
  | eq (T vs,T vs') = (List.all eq (ListPair.zip(vs,vs'))
                       handle _ => false)
  | eq _ = false

fun iota n = T (List.tabulate(n, R o Real.fromInt))

fun nth v n =
   case unT v of
      SOME vs => List.nth(vs, n)
    | NONE    => die "nth: must have an array argument"

type 'a f = v -> 'a

fun pp_f _ _  = "<fun>"

fun mk_fM f = f

val mk_f = mk_fM

fun fmap_f f fa = f o fa

fun mapM (f:v -> v M) (vs:v) : v M =
    case unT vs of
        SOME vs' => T (List.map f vs')
       | NONE  => die "mapM: map expects a list"

val map = mapM

fun mapP (xam : v -> 'a) (eval: 'a -> v) (vs:v) : v =
    map (eval o xam) vs

fun zipM (fs:(v -> v M) list) (vs:v) : v M =
    case unT vs of
        SOME vs' => T (ListPair.mapEq (fn (f, v) => f v) (fs, vs'))
       | NONE  => die "zipM: zip expects a list"

val zip = zipM

fun fold (s:string) (f: v -> v) (ne : v) : v -> v =
  fn T xs => foldl (fn (v1, v2) => f (T [v1,v2])) ne xs
     | v => die ("type error fold - expecting list (" ^ s ^ ") - got " ^ pp v)

val sum = fold "sum" add Z

fun red r v = T (List.map (sum o T o List.map (nth v) o Rel.toFunc r) (Rel.eval_index (Rel.domain r)))
end
