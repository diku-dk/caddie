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
  val fmap        : ('a -> 'b) -> 'a M -> 'b M
  val sequence    : ('a M) list -> ('a list) M

  val iota        : int -> v
  val nth         : v -> int -> v

  type 'a f
  val pp_f        : ('a -> string) -> 'a f -> string
  val mk_fM       : (v -> 'a M) -> ('a f) M
  val mk_f        : (v -> 'a) -> 'a f
  val fmap_f      : ('a -> 'b) -> 'a f -> 'b f
  val mapM        : (v -> v M) -> v -> v
  val map         : (v -> v) -> v -> v
  val mapP        : 'a f M -> ('a -> v M) -> v -> v
  val zipM        : (v -> v M) list -> v -> v M
  val zip         : (v -> v) list -> v -> v

  val red         : Rel.r -> v -> v
end
