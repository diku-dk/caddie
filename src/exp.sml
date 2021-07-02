functor Exp(structure V:VAL
            structure F:FUN
            sharing type V.v = F.v) : EXP where type f = F.f = struct
type f = F.f
type v = V.v
type var = string

datatype e =
         V of var
       | C of v
       | Uprim of Prim.uprim * e
       | Bilin of Prim.bilin * e * e
       | Add of e * e
       | Pair of e * e
       | Prj of int * e
       | If of e * e * e
       | Let of var * e * e
       | Apply of string * e
fun pp e =
    case e of
        V var => var
      | C v => V.pp v
      | Uprim(p,e) => Prim.pp_uprim p ^ "(" ^ pp e ^ ")"
      | Bilin(p,e1,e2) => "(" ^ pp e1 ^ Prim.pp_bilin p ^ pp e2 ^ ")"
      | Add(e1,e2) => "(" ^ pp e1 ^ "+" ^ pp e2 ^ ")"
      | Pair(e1,e2) => "(" ^ pp e1 ^ "," ^ pp e2 ^ ")"
      | Prj(i,e) => "#" ^ Int.toString i ^ "(" ^ pp e ^ ")"
      | If(e,e1,e2) => "(if " ^ pp e ^ " then " ^ pp e1 ^ " else " ^ pp e2 ^ ")"
      | Let(i,e1,e2) => "(let " ^ i ^ " = " ^ pp e1 ^ " in " ^ pp e2 ^ ")"
      | Apply (f,e) => "(" ^ f ^ "(" ^ pp e ^ "))"

fun lrangle (f,g) = F.Comp(F.FProd(f,g),F.Dup)
fun hat opr (f,g) = F.Comp(opr,lrangle(f,g))

fun mem x xs = List.exists (fn y => x=y) xs

type delta = (var * f) list

fun add (v,f,E) : delta =
    (v,f)::E

fun lookup (E:delta) v =
    case E of
        (k,f)::E => if v = k then SOME f
                    else lookup E v
      | nil => NONE

fun push f E : delta =
    map (fn (x,g) => (x,F.Comp(g,f))) E

fun init (xs:var list) : delta =
    let val n = List.length xs
    in rev(#2(List.foldl (fn (x,(i,acc)) => (i+1,(x, F.Prj(n,i+1))::acc)) (0,nil) xs))
    end

fun trans0 E e =
    case e of
        V "pi" => F.K (V.R (Math.pi))
      | V x => (case lookup E x of
                    SOME f => f
                  | NONE => die ("trans: unbound variable " ^ x))
      | C v => F.K v
      | Uprim(p,e) => F.Comp (F.Uprim p, trans0 E e)
      | Bilin(p,e1,e2) => hat (F.Bilin p) (trans0 E e1,trans0 E e2)
      | Add(e1,e2) => hat F.Add (trans0 E e1,trans0 E e2)
      | Pair(e1,e2) => lrangle (trans0 E e1,trans0 E e2)
      | If (e,e1,e2) => F.If(trans0 E e,trans0 E e1,trans0 E e2)
      | Let(i,e1,e2) => F.Comp(trans0 (add(i,F.Prj(2,1),push(F.Prj(2,2))E)) e2,
                               F.Comp(F.FProd(trans0 E e1,F.Id),F.Dup))
      | Prj(i,e) => F.Comp (F.Prj(2,i),trans0 E e)
      | Apply(f,e) => F.Comp (F.DSL.named f, trans0 E e)

fun trans (vs:var list) e =
    trans0 (init vs) e

fun snart (vs:var list) f =
    let fun s f (e:e) =
            case f of
                F.K v => C v
              | F.Prj(1,1) => e
              | F.Prj(_,i) => (case e of
                                   Pair(a,b) =>
                                   if i=1 then a
                                   else if i=2 then b
                                   else die ("snart.Pair.Prj(" ^ Int.toString i ^ ")")
                                 | _ => Prj(i,e))
              | F.Add => Add(s (F.Prj(2,1)) e,
                             s (F.Prj(2,2)) e)
              | F.Comp(f,g) => s f (s g e)
              | F.FProd(f,g) =>
                (case e of
                     Pair(a,b) => Pair(s f a, s g b)
                   | _ => Pair(s f (Prj(1,e)),
                               s g (Prj(2,e))))
              | F.Id => e
              | F.Dup => Pair(e,e)
              | F.Uprim p => Uprim(p,e)
              | F.Bilin p => Bilin(p,s (F.Prj(2,1)) e,s (F.Prj(2,2)) e)
              | F.If(f,g,h) => If(s f e,s g e,s h e)
              | F.NamedFun f => Apply(f,e)
    in case vs of
           [x,y] => s f (Pair(V x, V y))
         | [x] => s f (V x)
         | _ => die "snart: expecting one or two parameters"
    end

structure DSL = struct
  val ln : e -> e = fn e => Uprim(Prim.Ln,e)
  val sin : e -> e = fn e => Uprim(Prim.Sin,e)
  val cos : e -> e = fn e => Uprim(Prim.Cos,e)
  val exp : e -> e = fn e => Uprim(Prim.Exp,e)
  fun pow (r: real) : e -> e = fn e => Uprim(Prim.Pow r,e)
  val ~ : e -> e = fn e => Uprim(Prim.Neg,e)
  val op + : e * e -> e = Add
  val op * : e * e -> e = fn (x,y) => Bilin(Prim.Mul,x,y)
  val op - : e * e -> e  = fn (x,y) => x + (~y)
  val const : v -> e = C
  val x1 : e = V "x1"
  val x2 : e = V "x2"
  val Y = V
  val rec V = fn i => Y i  (* eliminate constructor status *)
  val iff : e * e * e -> e = If
  val lett : string * e * e -> e = Let
  fun tup [e1,e2] = Pair(e1,e2)
    | tup _ = die "tup:expecting two elements"
  val prj = Prj
  val apply = Apply
end
end
