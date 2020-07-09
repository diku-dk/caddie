signature EXP = sig
  type v
  type e
  type f
  val pp : e -> string
  val trans : e -> f
  val snart : f -> e

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
  end
end
