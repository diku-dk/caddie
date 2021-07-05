signature VAL = sig

  type v
  val R           : real -> v
  val T           : v list -> v
  val VarOpt      : (string -> v) option

  val unT         : v -> v list option
  val unR         : v -> real option
  val isZ         : v -> bool

  val pp          : v -> string
  val prjI        : string -> int -> v -> v
  val add         : v -> v
  val Z           : v
  val uprim       : Prim.uprim -> v -> v
  val uprim_diff  : Prim.uprim -> v -> v
  val bilin       : Prim.bilin * v -> v

  val isComplex   : v -> bool

  type 'a M
  val ret         : 'a -> 'a M
  val >>=         : 'a M * ('a -> 'b M) -> 'b M
  val letBind     : v -> v M
  val iff         : v * v M * v M -> v
  val ppM         : string -> ('a -> string) -> 'a M -> string
  val getVal      : 'a M -> 'a
  val eq          : v * v -> bool
end
