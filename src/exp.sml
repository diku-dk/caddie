functor Exp(structure V:VAL
            structure F:FUN
            sharing type V.v = F.v) : EXP where type f = F.f = struct
type f = F.f
type v = V.v
type var = int

datatype e =
         X of int
       | C of v
       | Uprim of Prim.uprim * e
       | Bilin of Prim.bilin * e * e
       | Add of e * e
       | Pair of e * e
       | If of e * e * e
       | Let of var * e * e

fun pp e =
    case e of
        X i => "x" ^ Int.toString i
      | C v => V.pp v
      | Uprim(p,e) => Prim.pp_uprim p ^ "(" ^ pp e ^ ")"
      | Bilin(p,e1,e2) => "(" ^ pp e1 ^ Prim.pp_bilin p ^ pp e2 ^ ")"
      | Add(e1,e2) => "(" ^ pp e1 ^ "+" ^ pp e2 ^ ")"
      | Pair(e1,e2) => "(" ^ pp e1 ^ "," ^ pp e2 ^ ")"
      | If(e,e1,e2) => "(if " ^ pp e ^ " then " ^ pp e1 ^ " else " ^ pp e2 ^ ")"
      | Let(i,e1,e2) => "(let x" ^ Int.toString i ^ " = " ^ pp e1 ^ " in " ^ pp e2 ^ ")"

fun lrangle (f,g) = F.Comp(F.FProd(f,g),F.Dup)
fun hat opr (f,g) = F.Comp(opr,lrangle(f,g))

fun mem x xs = List.exists (fn y => x=y) xs

fun max_x vs m e =
    case e of
        X i => if mem i vs orelse m>i then m else i
      | C v => m
      | Uprim(p,e) => max_x vs m e
      | Bilin(p,e1,e2) => max_x vs (max_x vs m e1) e2
      | Add(e1,e2) => max_x vs (max_x vs m e1) e2
      | Pair(e1,e2) => max_x vs (max_x vs m e1) e2
      | If(e,e1,e2) => max_x vs (max_x vs (max_x vs m e) e1) e2
      | Let(i,e1,e2) => max_x (i::vs) (max_x vs m e1) e2

type delta = (var * f) list

fun add (v,f,E) =
    (v,f)::E

fun lookup E v =
    case E of
        (k,f)::E => if v = k then SOME f
                    else lookup E v
      | nil => NONE

fun push f E =
    map (fn (x,g) => (x,F.Comp(g,f))) E

fun init n =
    List.tabulate(n, fn i => (i+1,F.Prj(n,i+1)))

fun trans0 E e =
    case e of
        X i => (case lookup E i of
                    SOME f => f
                  | NONE => die ("trans: unbound variable x" ^ Int.toString i))
      | C v => F.K v
      | Uprim(p,e) => F.Comp (F.Uprim p, trans0 E e)
      | Bilin(p,e1,e2) => hat (F.Bilin p) (trans0 E e1,trans0 E e2)
      | Add(e1,e2) => hat F.Add (trans0 E e1,trans0 E e2)
      | Pair(e1,e2) => lrangle (trans0 E e1,trans0 E e2)
      | If (e,e1,e2) => F.If(trans0 E e,trans0 E e1,trans0 E e2)
      | Let(i,e1,e2) => F.Comp(trans0 (add(i,F.Prj(2,1),push(F.Prj(2,2))E)) e2,
                               F.Comp(F.FProd(trans0 E e1,F.Id),F.Dup))

fun trans e =
    let val m = max_x nil 0 e
    in trans0 (init m) e
    end

fun snart f =
    let fun s f (e:e) =
            case f of
                F.K v => C v
              | F.Prj(_,i) => (case e of
                                   X ~1 => X i
                                 | Pair(a,b) =>
                                   if i=1 then a
                                   else if i=2 then b
                                   else die ("snart.Pair.Prj(" ^ Int.toString i ^ ")")
                                 | _ =>  die ("snart.Prj(" ^ Int.toString i ^ ")"))
              | F.Add => Add(s (F.Prj(2,1)) e,
                             s (F.Prj(2,2)) e)
              | F.Comp(f,g) => s f (s g e)
              | F.FProd(f,g) =>
                (case e of
                     X ~1 => Pair(s f (X 1), s g (X 2))
                   | Pair(a,b) => Pair(s f a, s g b)
                   | _ => die "snart.FProd")
              | F.Id => e
              | F.Dup => Pair(e,e)
              | F.Uprim p => Uprim(p,e)
              | F.Bilin p => Bilin(p,s (F.Prj(2,1)) e,s (F.Prj(2,2)) e)
              | F.If(f,g,h) => If(s f e,s g e,s h e)
    in s f (X ~1)
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
  val x1 : e = X 1
  val x2 : e = X 2
  val Y = X
  val rec X = fn i => Y i
  val iff : e * e * e -> e = If
  val lett : int * e * e -> e = Let
end
end
