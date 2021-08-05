fun die s = (print ("Error (Prim): " ^ s ^ "\n"); raise Fail s)

structure Prim :> PRIM = struct
  datatype uprim = Sin | Cos | Ln | Exp | Pow of real | Neg

  fun real_to_string r =
      let val s = CharVector.map (fn #"~" => #"-" | c => c) (Real.toString r)
      in if size s >= 2
            andalso String.sub(s,size s - 1) = #"0"
            andalso String.sub(s,size s - 2) = #"."
         then String.extract (s,0,SOME(size s - 2))
         else s
      end

  fun pp_uprim (p: uprim) : string =
      case p of
          Sin => "sin"
        | Cos => "cos"
        | Ln => "ln"
        | Exp => "exp"
        | Neg => "~"
        | Pow r => "pow(" ^ real_to_string r ^ ")"
  datatype bilin = Mul     (* : R x R -> R             multiplication *)
                 | Cprod3  (* : R3 x R3 -2> R3         cross product *)
                 | Dprod   (* : RN x RN -2> R          dot product *)
                 | Sprod   (* : R x RN -2> RN          scalar product *)
                 | Norm2Sq (* : R x R -> R             \(x,y).(x^2+y^2) *)
  fun pp_bilin b =
      case b of
          Mul => "*"    (* all to be printed infix *)
        | Cprod3 => "x"
        | Dprod => "dot"
        | Sprod => "."
        | Norm2Sq => "norm2sq"

  val mul : real * real -> real = op *
  fun cprod3 ([a1,a2,a3], [b1,b2,b3]) : real list =
    [a2*b3-a3*b2, a3*b1-a1*b3, a1*b2-a2*b1]
    | cprod3 _ = die "cprod3 expects two triples of reals"

  fun dprod (rs1, rs2) : real =
      let val ps = List.map mul (ListPair.zip (rs1,rs2))
      in List.foldl (fn (v,a) => v + a) 0.0 ps
      end handle _ => die "dprod expects equal length tuples"

  fun sprod (s,rs) = List.map (fn v => mul(s,v)) rs

  fun norm2sq (x,y) : real = x*x+y*y

  fun uprim p : real -> real =
      case p of
          Sin => Math.sin
        | Cos => Math.cos
        | Ln => Math.ln
        | Exp => Math.exp
        | Neg => Real.~
        | Pow r => (fn x => Math.pow(x,r))

  val eq_bilin : bilin * bilin -> bool = op =
  val eq_uprim : uprim * uprim -> bool =
   fn (Sin,Sin) => true
    | (Cos,Cos) => true
    | (Ln,Ln) => true
    | (Exp,Exp) =>  true
    | (Neg,Neg) => true
    | (Pow r,Pow r') => Real.==(r,r')
    | _ => false

end
