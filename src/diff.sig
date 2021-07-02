signature DIFF = sig
  type v
  structure L : LIN where type v = v
  structure F : FUN where type v = v

  type env = (string * F.f) list
  type 'a M
  val diff  : env -> F.f -> v -> v * L.lin
  val diffM : env -> F.f -> v -> (v * L.lin) M
end
