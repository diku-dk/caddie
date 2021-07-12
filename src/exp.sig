signature EXP = sig
  type v
  type e
  type f
  type var
  val pp : e -> string
  val trans : var list -> e -> f
  val snart : var list -> f -> e

  structure DSL : sig
    val ln : e -> e
    val sin : e -> e
    val cos : e -> e
    val exp : e -> e
    val pow : real -> e -> e
    val ~ : e -> e
    val + : e * e -> e
    val * : e * e -> e
    val - : e * e -> e
    val const : v -> e
    val x1 : e
    val x2 : e
    val V : var -> e
    val tup : e list -> e
    val prj : int * int * e -> e
    val iff : e * e * e -> e
    val lett : string * e * e -> e
    val apply : string * e -> e
    val cprod3 : e -> e
    val dprod : e -> e
    val sprod : e -> e
    val norm2sq : e -> e
    val map : var * e * e -> e
    val red : Rel.r * e -> e
  end
end
