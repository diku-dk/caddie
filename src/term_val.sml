fun die s = (print ("Error (TermVal): " ^ s ^ "\n"); raise Fail s)

structure TermVal = struct

type var = string

datatype v = R of real
           | T of v list
           | Uprim of Prim.uprim * v
           | Add of v * v
           | Var of var
           | Bilin of Prim.bilin * v * v
           | If of v * v M * v M
           | Z
           | Prj of int * v
           | Map of var * v M * v
           | Zip of var * v list * v
           | Nth of v * int
           | Red of Rel.r * v
withtype 'a M = 'a * (string * v)list

val VarOpt = SOME Var

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

fun ppM0 (ind:string) (pp:v->string) (pp0:'a -> string) ((x,bs): 'a M) : string =
    case bs of
        nil => ind ^ pp0 x
      | _ => let val bs = List.map (fn (var,v) => ind ^ "let " ^ var ^ " = " ^ pp v) bs
             in String.concatWith "\n" bs ^ "\n" ^ ind ^ "in " ^ pp0 x
             end
fun pp v =
    case v of
        R r => real_to_string r
      | T vs => "(" ^ String.concatWith "," (map pp vs) ^ ")"
      | Uprim(p,v) => Prim.pp_uprim p ^ "(" ^ pp v ^ ")"
      | Add(v1,v2) => "(" ^ pp v1 ^ " + " ^ pp v2 ^ ")"
      | Bilin(p,v1,v2) => "(" ^ pp v1 ^ " " ^ Prim.pp_bilin p ^ " " ^ pp v2 ^ ")"
      | Var v => v
      | If(v,m1,m2) => "(if " ^ pp v ^ " then\n" ^ ppM0 "  " pp pp m1 ^ "\nelse\n" ^ ppM0 "  " pp pp m2 ^ ")"
      | Z => "Z"
      | Prj(i,v) => "prj" ^ Int.toString i ^ "(" ^ pp v ^ ")"
      | Map(x,f,vs) => "(map (fn " ^ x ^ " => " ^ ppM0 "" pp pp f ^ ") " ^ pp vs ^ ")"
      | Zip (x,fs,vs) => "(zip [" ^ String.concatWith "," (map (fn f => "fn " ^ x ^ " => " ^ pp f) fs) ^ "])"
      | Nth(v,n) => pp v ^ "[" ^ Int.toString n ^ "]"
      | Red(r,v)  => "red(" ^ Rel.pp r ^ "," ^ pp v ^ ")"

fun ppM (ind:string) (pp0:'a -> string) (m: 'a M) : string =
    ppM0 ind pp pp0 m

fun iff (v,m1,m2) = If(v,m1,m2)

fun prjI (s:string) (i:int) : v -> v =
    fn T xs => (List.nth(xs,i-1) handle _ => die (s ^ " index error"))
     | v => Prj(i,v)

(* smart constructor for Add *)
fun add (T[v1,v2]) =
    let fun add0 (v1,v2) =
            case (v1,v2) of
                (Z,v2) => v2
              | (v1,Z) => v1
              | (R r1,R r2) => R(r1+r2)
              | (T vs1,T vs2) =>
                (T(ListPair.mapEq add0 (vs1,vs2))
                 handle _ => die "add0.unequal sized tuples")
              | (R _, T _) => die "add0.type mismatch R-T"
              | (T _, R _) => die "add0.type mismatch T-R"
              | _ => Add(v1,v2)
    in add0 (v1,v2)
    end
  | add _ = die "add: expecting pair as argument"

fun mul (R a,R b) = R (a*b)
  | mul (Z,_) = Z
  | mul (_,Z) = Z
  | mul (T vs1,T vs2) = T (map mul (ListPair.zip (vs1,vs2)))
  | mul (v1,v2) = Bilin(Prim.Mul,v1,v2)

fun cprod3 (T [R a1,R a2,R a3], T [R b1,R b2,R b3]) : v =
    T(map R (Prim.cprod3([a1,a2,a3],[b1,b2,b3])))
  | cprod3 (a,b) = Bilin(Prim.Cprod3,a,b)

exception Stop
fun dprod (T vs1, T vs2) : v =
    (let fun unR (R r) = r
           | unR _ = raise Stop
     in R(Prim.dprod (map unR vs1, map unR vs2))
     end handle Stop => Bilin(Prim.Dprod,T vs1,T vs2))
  | dprod (a,b) = Bilin(Prim.Dprod,a,b)

fun sprod (R s,T vs) =
    (let fun unR (R r) = r
           | unR _ = raise Stop
     in T(map R (Prim.sprod (s,map unR vs)))
     end handle Stop => Bilin(Prim.Sprod,R s,T vs))
  | sprod (R s, R v) = R(s*v)
  | sprod (s,v) = Bilin(Prim.Sprod,s,v)

fun norm2sq (R x,R y) : v = R(Prim.norm2sq(x,y))
  | norm2sq (Z, R y) : v = R(Prim.norm2sq(0.0,y))
  | norm2sq (R x, Z) : v = R(Prim.norm2sq(x,0.0))
  | norm2sq (v1, v2) = Bilin(Prim.Norm2Sq,v1,v2)
(*    die ("norm2sq expects two real values - received " ^ pp v1 ^ " and " ^ pp v2)*)

fun bilin0 p : v * v -> v =
    case p of
        Prim.Cprod3 => cprod3
      | Prim.Dprod => dprod
      | Prim.Sprod => sprod
      | Prim.Mul => mul
      | Prim.Norm2Sq => norm2sq

fun uprim (p: Prim.uprim) : v -> v =
    fn R r => R (Prim.uprim p r)
     | Z => R (Prim.uprim p 0.0)
     | T vs => T (map (uprim p) vs)
     | v => Uprim (p,v)

val var = Var

local val t = ref 0
in fun tick_reset() = t := 0
   fun tick() = t:= !t + 1
   fun tick_read() = !t
end

fun simpl0 v =
    case v of
        Add(R r1,R r2) => (tick(); R (r1+r2))
      | Add(Z,v2) => (tick(); simpl0 v2)
      | Add(v1,Z) => (tick(); simpl0 v1)
      | Add(R r,v) => if Real.==(r,0.0) then (tick(); simpl0 v)
                      else Add(R r,simpl0 v)
      | Add(v,R r) => if Real.==(r,0.0) then (tick(); simpl0 v)
                      else Add(simpl0 v,R r)
      | Add(T vs1,T vs2) => (tick(); T(map (fn (v1,v2) => simpl0 (Add(v1,v2))) (ListPair.zip(vs1,vs2))))
      | Add(v1,v2) => Add(simpl0 v1,simpl0 v2)
      | Uprim (Prim.Pow r,v) =>
        if Real.==(r,1.0) then (tick(); simpl0 v)
        else if Real.==(r,0.0) then (tick(); R 1.0)
        else Uprim(Prim.Pow r, simpl0 v)
      | Uprim (Prim.Neg, Z) => (tick(); Z)
      | Uprim (Prim.Neg, R r) => (tick(); R (~r))
      | Uprim (Prim.Neg, T vs) => (tick(); T (map (fn v => simpl0(Uprim(Prim.Neg, v))) vs))
      | Uprim (Prim.Neg, v) => Uprim(Prim.Neg, simpl0 v)
      | Uprim (p,v) => Uprim(p, simpl0 v)
      | T vs => T (map simpl0 vs)
      | R _ => v
      | Z => Z
      | Prj(i,T vs) => (tick();
                        simpl0 (List.nth(vs,i-1))
                        handle _ => die "simpl0.Prj.projection out of bound")
      | Var _ => v
      | Bilin(Prim.Mul,R r1,R r2) => (tick(); R (r1*r2))
      | Bilin(Prim.Mul,R r,v) => if Real.==(r,0.0) then (tick(); R 0.0)
                                 else if Real.==(r,1.0) then (tick(); simpl0 v)
                                 else Bilin(Prim.Mul,R r,simpl0 v)
      | Bilin(Prim.Mul,v,R r) => if Real.==(r,0.0) then (tick(); R 0.0)
                                 else if Real.==(r,1.0) then (tick(); simpl0 v)
                                 else Bilin(Prim.Mul,simpl0 v,R r)
      | Bilin(Prim.Mul,Z,v2) => (tick(); Z)
      | Bilin(Prim.Mul,v1,Z) => (tick(); Z)
      | Bilin(Prim.Mul,v1,v2) => Bilin(Prim.Mul,simpl0 v1,simpl0 v2)
      | Bilin(p,v1,v2) => Bilin(p,simpl0 v1,simpl0 v2)
      | If(v,m1,m2) => If(simpl0 v,simplM m1,simplM m2)
      | Prj(i,v) => Prj(i,simpl0 v)
      | Map(x, f, vs)  => Map (x, simplM f, simpl0 vs)
      | Zip(x,fs,vs)  => Zip(x, map simpl0 fs, simpl0 vs)
      | Nth(v,n)  => Nth(simpl0 v, n)
      | Red (r, v) => Red(r, simpl0 v)
and simplM (v,bs) = (simpl0 v,map (fn (x,v) => (x,simpl0 v)) bs)

fun simpl1 e =
    let val () = tick_reset()
        val e' = simpl0 e
    in if tick_read() > 0 then simpl1 e'
       else e'
    end

fun eq (a,b) =
    case (a,b) of
        (R a, R b) => abs (a-b) < 0.0000001
      | (Z,Z) => true
      | (T vs1, T vs2) => List.all (fn x => x) (List.map eq (ListPair.zip (vs1,vs2)))
      | (Var v, Var v') => v=v'
      | (Uprim (p, v), Uprim (p',v')) => Prim.eq_uprim (p,p') andalso eq (v, v')
      | (Add (v1,v2), Add(v1',v2')) => eq(v1,v1') andalso eq(v2,v2')
      | (Bilin (p,v1,v2),Bilin (p',v1',v2')) => Prim.eq_bilin(p,p') andalso eq(v1,v1') andalso eq(v2,v2')
      | _ => false

fun subst S e =
    case e of
        Var k =>
        (case List.find (fn (k0,_) => k=k0) S of
             SOME (k0,v0) => v0
           | NONE => e)
      | Z => Z
      | R _ => e
      | T es => T(map (subst S) es)
      | Prj(i,e) => Prj(i,subst S e)
      | Uprim(p,e) => Uprim(p,subst S e)
      | Add(e1,e2) => Add(subst S e1, subst S e2)
      | Bilin(p,e1,e2) => Bilin(p,subst S e1, subst S e2)
      | If(v,m1,m2) => If (subst S v,
                           substM S m1,
                           substM S m2)
      | Map (x, f, v)  => Map (x, substM S f, subst S v)
      | Zip (x, fs, vs)  => Zip (x, fs, subst S vs)
      | Nth (v, n)  =>  Nth (subst S v, n)
      | Red (r, v)  => Red (r, subst S v)

and substM S (v,bs) =
    (subst S v,map (fn (x,e) => (x,subst S e)) bs)

fun combine S ca nil = (S,ca)
  | combine S ca ((k,v)::rest) =
    let val v = subst S v
        val v = simpl1 v
    in case List.find (fn (_,v0) => eq (v,v0)) ca of
           SOME (k0,v0) =>
           let val S' = (k,Var k0)::S
           in combine S' ca rest
           end
         | NONE =>
           case v of
               Var _ => combine ((k,v)::S) ca rest
             | R _ => combine ((k,v)::S) ca rest
             | _ => combine S (ca@[(k,v)]) rest
    end

fun simpl (e,bs) =
    let val (S,bs) = combine nil nil bs
    in (simpl1 (subst S e), bs)
    end

fun bilin (p,v:v) : v =
    case unT v of
        SOME [v1,v2] => bilin0 p (v1,v2)
      | _ => die ("type error bilin (" ^ Prim.pp_bilin p ^ ") - expecting pair - got " ^ pp v)


fun uprim_diff (p: Prim.uprim) (x:v) : v =
    case p of
        Prim.Sin => uprim Prim.Cos x
      | Prim.Cos => uprim Prim.Neg (uprim Prim.Sin x)
      | Prim.Ln => uprim (Prim.Pow ~1.0) x
      | Prim.Exp => uprim Prim.Exp x
      | Prim.Neg => uprim Prim.Neg x
      | Prim.Pow r => bilin0 Prim.Mul (R r,uprim (Prim.Pow(r-1.0)) x)

fun isComplex v =
    case v of
        R _ => false
      | Z => false
      | Var _ => false
      | T vs => false
      | Uprim (p,v) => true
      | Add _ => true
      | Bilin _ => true
      | If _ => true
      | Prj _ => true
      | Map _ =>  true
      | Zip _  =>  true
      | Nth (v,_) =>  isComplex v
      | Red _  =>  true

val newVar =
    let val c = ref 0
    in fn () => (c:= !c + 1; "v" ^ Int.toString (!c))
    end

infix >>=
fun ((a,ca) : 'a M) >>= (f: 'a -> 'b M) : 'b M =
    let val (b,cb) = f a
        (*val (S,c) = combine nil ca cb*)
    in (b,ca@cb)
    end
fun ret (x:'a) = (x,nil)

fun letBind (v:v) : v M =
    if isComplex v then
      let val var = newVar()
      in (Var var, [(var,v)])
      end
    else ret v

val getVal = fn (x,_) => x

val fmap : ('a -> 'b) -> 'a M -> 'b M = fn f => fn m =>  m >>= (fn x => ret (f x))

fun sequence (mas : ('a M) list) =
    case mas of
         nil => ret nil
       | (ma :: mas') =>
           ma >>= (fn a =>
           sequence mas' >>= (fn as' =>
           ret (a :: as')))

fun iota n = T (List.tabulate(n, R o Real.fromInt))

fun nth v n = Nth(v,n)

type 'a f = var * 'a

fun pp_f pp_a (var, a) = "pm " ^ var ^ " => " ^ pp_a a

fun mk_fM f =
 let val x = newVar()
 in f (Var x) >>= (fn fx => ret (x, fx))
 end

fun mk_f f = getVal (mk_fM (ret o f))

fun fmap_f g (x, f) = (x, g f)

fun mapM (f:v -> v M) (vs:v) : v =
    let val x = newVar()
    in Map(x, f (Var x), vs)
    end

fun map (f:v -> v) = mapM (ret o f)

fun mapP (xam : 'a f M) (eval:'a -> v M) (vs:v) : v =
    let val f' = xam >>= (fn (x, a) => eval a)
        val x = #1 (getVal xam)
    in Map(x, f', vs)
    end

fun zipM (fs:(v -> v M) list) (vs:v) : v M =
    let val x = newVar()
    in sequence (List.map (fn f => f (Var x)) fs) >>= (fn fs' => ret(Zip(x,fs',vs)))
    end

fun zip (fs : (v -> v) list) =
    getVal o zipM ((List.map (fn f => ret o f)) fs)

fun red (r: Rel.r) (v:v) = Red (r,v)
end
