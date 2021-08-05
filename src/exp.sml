functor Exp(structure V:VAL
            structure F:FUN
            sharing type V.v = F.v) : EXP where type f = F.f = struct

(* Some utilities *)
fun mapi f xs =
    let fun loop n nil = nil
          | loop n (x::xs) = f(x,n) :: loop (n+1) xs
    in loop 0 xs
    end

type f = F.f
type v = V.v
type var = string

datatype e =
         Var of var
       | Const of v
       | Uprim of Prim.uprim * e
       | Bilin of Prim.bilin * e * e
       | Add of e * e
       | Tuple of e list
       | Prj of int * int * e
       | If of e * e * e
       | Let of var * e * e
       | Apply of string * e
       | Map of var * e * e
       | Red of Rel.r * e

fun pp e =
    case e of
        Var var => var
      | Const v => V.pp v
      | Uprim(p,e) => Prim.pp_uprim p ^ "(" ^ pp e ^ ")"
      | Bilin(p,e1,e2) => "(" ^ pp e1 ^ Prim.pp_bilin p ^ pp e2 ^ ")"
      | Add(e1,e2) => "(" ^ pp e1 ^ "+" ^ pp e2 ^ ")"
      | Tuple es => "(" ^ String.concatWith "," (map pp es) ^ ")"
      | Prj(2,1,e) => "#1(" ^ pp e ^ ")"
      | Prj(2,2,e) => "#2(" ^ pp e ^ ")"
      | Prj(n,i,e) => "#" ^ Int.toString i ^ "{of " ^ Int.toString n ^ "}(" ^ pp e ^ ")"
      | If(e,e1,e2) => "(if " ^ pp e ^ " then " ^ pp e1 ^ " else " ^ pp e2 ^ ")"
      | Let(x,e1,e2) => "let " ^ x ^ " = " ^ pp e1 ^ " in " ^ pp e2 ^ " end"
      | Apply (f,e) => "(" ^ f ^ "(" ^ pp e ^ "))"
      | Map(x,f,es)  => "(map (fn " ^ x ^ " => " ^ pp f ^ ") " ^ pp es ^ ")"
      | Red(r,e) => "(red " ^ Rel.pp r ^ " " ^ pp e ^ ")"

fun lrangle [f] = f
  | lrangle fs = F.Comp(F.FProd fs,F.Dup (length fs))

fun hat opr (f,g) = F.Comp(opr,lrangle[f,g])

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
        Var "pi" => F.K (V.R (Math.pi))
      | Var x => (case lookup E x of
                      SOME f => f
                    | NONE => die ("trans: unbound variable " ^ x))
      | Const v => F.K v
      | Uprim(p,e) => F.Comp (F.Uprim p, trans0 E e)
      | Bilin(p,e1,e2) => hat (F.Bilin p) (trans0 E e1,trans0 E e2)
      | Add(e1,e2) => hat F.Add (trans0 E e1,trans0 E e2)
      | Tuple es => lrangle (map (trans0 E) es)
      | If (e,e1,e2) => F.If(trans0 E e,trans0 E e1,trans0 E e2)
      | Let(i,e1,e2) => F.Comp(trans0 (add(i,F.Prj(2,1),push(F.Prj(2,2))E)) e2,
                               F.Comp(F.FProd[trans0 E e1,F.Id],F.Dup 2))
      | Prj(n,i,e) => F.Comp (F.Prj(n,i),trans0 E e)
      | Apply(f,e) => F.Comp (F.DSL.named f, trans0 E e)
      | Map(x,f,e) => F.Comp(F.Map (trans0 (init [x]) f), trans0 E e)
      | Red(r,e) => F.Comp(F.Red r, trans0 E e)

fun trans (vs:var list) e =
    trans0 (init vs) e

fun snart (vs:var list) f =
    let fun s f (e:e) =
            case f of
                F.K v => Const v
              | F.Prj(1,1) => e
              | F.Prj(n,i) => (case e of
                                   Tuple es =>
                                   (List.nth(es,i-1)
                                    handle _ => die ("snart.Tuple.Prj(" ^ Int.toString i ^ ")"))
                                 | _ => Prj(n,i,e))
              | F.Add => Add(s (F.Prj(2,1)) e,
                             s (F.Prj(2,2)) e)
              | F.Comp(f,g) => s f (s g e)
              | F.FProd fs =>
                (case e of
                     Tuple xs => Tuple(ListPair.map (fn (f,x) => s f x) (fs,xs))
                   | _ =>
                     let val n = length fs
                         val ps = List.tabulate (n,
                                                 fn i => Prj(n,i+1,e))
                     in Tuple (ListPair.map (fn (f,p) => s f p) (fs,ps))
                     end)
              | F.Id => e
              | F.Dup n => Tuple (List.tabulate(n, fn _ => e))
              | F.Uprim p => Uprim(p,e)
              | F.Bilin p => Bilin(p,s (F.Prj(2,1)) e,s (F.Prj(2,2)) e)
              | F.If(f,g,h) => If(s f e,s g e,s h e)
              | F.NamedFun f => Apply(f,e)
	      | F.Map f => Map ("x", s f (Var "x"), e)
              | F.Red r => Red(r,e)
    in case vs of
           [x] => s f (Var x)
         | _ => s f (Tuple (map Var vs))
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
  val const : v -> e = Const
  val x1 : e = Var "x1"
  val x2 : e = Var "x2"
  val V = Var
  val iff : e * e * e -> e = If
  val lett : string * e * e -> e = Let
  val tup = Tuple
  val prj = Prj
  val apply = Apply
  val op * : e * e -> e = fn (x,y) => Bilin(Prim.Mul,x,y)
  val cprod3 = fn e => Bilin(Prim.Cprod3,prj(2,1,e),prj(2,2,e))
  val dprod = fn e => Bilin(Prim.Dprod,prj(2,1,e),prj(2,2,e))
  val sprod = fn e => Bilin(Prim.Sprod,prj(2,1,e),prj(2,2,e))
  val norm2sq = fn e => Bilin(Prim.Norm2Sq,prj(2,1,e),prj(2,2,e))
  val map = Map
  val red = Red
end
end
