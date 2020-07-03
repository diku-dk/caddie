signature FUN = sig
  type v
  datatype f =
         Comp of f * f       (* X -> Y *)
       | Prj of int          (* X1*...*Xn->Xi *)
       | Add                 (* R*R->R *)
       | K of v              (* X -> Y *)
       | FProd of f * f      (*A*B->C*D*)
       | Dup                 (* X->X*X *)
       | Id                  (* X -> X *)
       | Uprim of Prim.uprim
       | Bilin of Prim.bilin (* X*Y->Z *)

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
  end
end
