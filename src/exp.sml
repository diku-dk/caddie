functor Exp(structure V:VAL
            structure F:FUN
            sharing type V.v = F.v) : EXP where type f = F.f = struct
type f = F.f
type v = V.v
datatype e =
         X of int
       | C of v
       | Uprim of Prim.uprim * e
       | Bilin of Prim.bilin * e * e
       | Add of e * e
       | Pair of e * e

fun pp e =
    case e of
        X i => "x" ^ Int.toString i
      | C v => V.pp v
      | Uprim(p,e) => Prim.pp_uprim p ^ "(" ^ pp e ^ ")"
      | Bilin(p,e1,e2) => "(" ^ pp e1 ^ Prim.pp_bilin p ^ pp e2 ^ ")"
      | Add(e1,e2) => "(" ^ pp e1 ^ "+" ^ pp e2 ^ ")"
      | Pair(e1,e2) => "(" ^ pp e1 ^ "," ^ pp e2 ^ ")"

fun lrangle (f,g) = F.Comp(F.FProd(f,g),F.Dup)
fun hat opr (f,g) = F.Comp(opr,lrangle(f,g))

fun trans e =
    case e of
        X i => F.Prj i
      | C v => F.K v
      | Uprim(p,e) => F.Comp (F.Uprim p, trans e)
      | Bilin(p,e1,e2) => hat (F.Bilin p) (trans e1,trans e2)
      | Add(e1,e2) => hat F.Add (trans e1,trans e2)
      | Pair(e1,e2) => lrangle (trans e1,trans e2)

fun snart f =
    let fun s f (e:e) =
            case f of
                F.K v => C v
              | F.Prj i => (case e of
                                X ~1 => X i
                              | Pair(a,b) =>
                                if i=1 then a
                                else if i=2 then b
                                else die ("snart.Pair.Prj(" ^ Int.toString i ^ ")")
                              | _ =>  die ("snart.Prj(" ^ Int.toString i ^ ")"))
              | F.Add => Add(s (F.Prj 1) e,
                             s (F.Prj 2) e)
              | F.Comp(f,g) => s f (s g e)
              | F.FProd(f,g) =>
                (case e of
                     X ~1 => Pair(s f (X 1), s g (X 2))
                   | Pair(a,b) => Pair(s f a, s g b)
                   | _ => die "snart.FProd")
              | F.Id => e
              | F.Dup => Pair(e,e)
              | F.Uprim p => Uprim(p,e)
              | F.Bilin p => Bilin(p,s (F.Prj 1) e,s (F.Prj 2) e)
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
  val x1 : e = X 1
  val x2 : e = X 2
end
end
