
signature PRIM = sig
  datatype uprim = Sin | Cos | Ln | Exp | Pow of real | Neg
  val pp_uprim : uprim -> string

  datatype bilin = Mul     (* : R x R -2> R            multiplication *)
                 | Cprod3  (* : R3 x R3 -2> R3         cross product *)
                 | Dprod   (* : RN x RN -2> R          dot product *)
                 | Sprod   (* : R * RN -2> RN          scalar product *)
                 | Norm2Sq (* : R x R -2> R            \(x,y).(x^2+y^2) *)
  val pp_bilin : bilin -> string    (* all to be printed infix *)

  val mul      : real * real -> real
  val cprod3   : real list * real list -> real list
  val dprod    : real list * real list -> real
  val sprod    : real * real list -> real list
  val norm2sq  : real * real -> real

  val eq_bilin : bilin * bilin -> bool
  val eq_uprim : uprim * uprim -> bool
  val uprim : uprim -> real -> real
end
