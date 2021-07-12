signature FUN = sig
  type v
  datatype f =
         Comp of f * f       (* X -> Y *)
       | Prj of int * int    (* X1*...*Xn->Xi ; Prj(n,i) *)
       | Add                 (* R*R->R *)
       | K of v              (* X -> Y *)
       | FProd of f list     (* A1*...*An->B1*...*Bn *)
       | Dup of int          (* X->X*...*X *)
       | Id                  (* X -> X *)
       | Uprim of Prim.uprim
       | Bilin of Prim.bilin (* X*Y->Z *)
       | If of f * f * f
       | NamedFun of string
       | Map of f
       | Red of Rel.r

  val pp  : f -> string
  val opt : f -> f
  structure DSL : sig
    val x : f * f -> f
    val + : f
    val * : f
    val o : f * f -> f
    val sin  : f
    val cos  : f
    val exp  : f
    val ln   : f
    val pow  : real -> f
    val ~    : f
    val dup  : f
    val id   : f
    val iff  : f * f * f -> f  (* iff : (A->R)x(A->C)x(A->C) -> A -> C *)
    val named : string -> f
    val map  : f -> f
    val red  : Rel.r -> f
  end
end
