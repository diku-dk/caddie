signature DIFF = sig
  type v
  structure L : LIN where type v = v
  structure F : FUN where type v = v
  val diff : F.f -> v -> v * L.lin
end
