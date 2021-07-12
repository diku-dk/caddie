fun die s = (print ("Error (Fun): " ^ s ^ "\n"); raise Fail s)

functor Fun(V:VAL) :> FUN where type v = V.v = struct

type v = V.v
datatype f =
         Comp of f * f       (* X -> Y *)
       | Prj of int * int    (* X1*...*Xn->Xi ; Prj(n,i) *)
       | Add                 (* R*R->R *)
       | K of V.v            (* X -> Y *)
       | FProd of f list     (* A1*...*An->B1*...*Bn *)
       | Dup of int          (* X->X*...*X *)
       | Id                  (* X -> X *)
       | Uprim of Prim.uprim
       | Bilin of Prim.bilin
       | If of f * f * f
       | NamedFun of string
       | Map of f
       | Red of Rel.r

fun pp e =
    case e of
        Comp(f,g) => "(" ^ pp f ^ " o " ^ pp g ^ ")"
      | Id => "id"
      | Prj (d,i) => "pi_" ^ Int.toString i ^ "/" ^ Int.toString d
      | Add => "(+)"
      | K v => V.pp v
      | FProd fs => "(" ^ String.concatWith " x " (map pp fs) ^ ")"
      | Dup 2 => "dup"
      | Dup n => "dup" ^ Int.toString n
      | Uprim p => Prim.pp_uprim p
      | Bilin opr => "(" ^ Prim.pp_bilin opr ^ ")"
      | If(f,g,h) => "(if " ^ pp f ^ " then " ^ pp g ^ " else " ^ pp h ^ ")"
      | NamedFun f => f
      | Map f => "(map " ^ pp f ^ " )"
      | Red r => "red(" ^ Rel.pp r ^ ")"

local val t = ref 0
in fun tick_reset() = t := 0
   fun tick() = t:= !t + 1
   fun tick_read() = !t
end

fun opt0 e =
    case e of
        Comp(FProd[Prj(2,1),Prj(2,2)],Dup 2) => (tick(); Id)
      | Prj(1,1) => (tick(); Id)
      | Comp(Id,f) => (tick(); opt0 f)
      | Comp(f,Id) => (tick(); opt0 f)
      | Comp(f,g) => Comp(opt0 f,opt0 g)
      | FProd fs => FProd (map opt0 fs)
      | If(f,g,h) => If(opt0 f,opt0 g,opt0 h)
      | _ => e

fun opt e =
    let val () = tick_reset()
        val e' = opt0 e
    in if tick_read() > 0 then opt e'
       else e'
    end

structure DSL = struct
  val op x = fn (f,g) => FProd[f,g]
  val op + = Add
  val op * = Bilin Prim.Mul
  val op o = Comp
  val dup = Dup 2
  val id = Id
  val sin = Uprim Prim.Sin
  val cos = Uprim Prim.Cos
  val exp = Uprim Prim.Exp
  val ln = Uprim Prim.Ln
  fun pow r = Uprim (Prim.Pow r)
  val iff = If
  val ~ = Uprim Prim.Neg
  val named = NamedFun
  val map = Map
  val red = Red
end
end
