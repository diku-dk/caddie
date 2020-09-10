signature DIFF = sig
  type v
  structure L : LIN where type v = v
  structure F : FUN where type v = v

  type 'a M
  val diff  : F.f -> v -> v * L.lin
  val diffM : F.f -> v -> (v * L.lin) M
end
