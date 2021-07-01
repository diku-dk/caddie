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
    val iff : e * e * e -> e
    val lett : string * e * e -> e
  end
end
