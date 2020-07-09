signature LIN = sig
  type v
  type lin
  type 'a M

  (* Constructors *)
  val lin   : string * (v -> v) -> lin
  val prj   : int -> lin
  val zero  : lin
  val id    : lin
  val oplus : lin * lin -> lin
  val comp  : lin * lin -> lin
  val curL  : Prim.bilin * v -> lin
  val curR  : Prim.bilin * v -> lin

  val pp    : lin -> string
  val eval  : lin -> v -> v M
  val seq   : lin -> lin list
end
