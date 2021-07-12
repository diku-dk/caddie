signature LIN = sig
  type v
  type 'a f
  type lin
  type 'a M

  (* Constructors *)
  val lin     : string * (v -> v) -> lin
  val prj     : int -> int -> lin   (* prj dim idx *)
  val zero    : lin
  val id      : lin
  val oplus   : lin list -> lin     (* n-ary oplus *)
  val comp    : lin * lin -> lin
  val curL    : Prim.bilin * v -> lin   (* ( v * ) *)
  val curR    : Prim.bilin * v -> lin   (* ( * v ) *)
  val lmap    : lin -> lin
  val zip     : lin list -> lin
  val lmapP   : lin f M * v -> lin
  val red   : Rel.r -> lin

  (* some linear primitives *)
  val add   : int -> lin              (* n-ary add *)
  val dup   : int -> lin              (* n-ary dup *)
  val neg   : lin

  val iff   : v * lin M * lin M -> lin

  val pp    : lin -> string
  val eval  : lin -> v -> v M

  val adjoint : lin -> lin
end
