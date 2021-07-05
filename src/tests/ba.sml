val () = print "****\n**** BA (Bundle Adjustment)\n****\n"
structure Ad = AD(TermVal)
open Ad
structure V = TermVal

infix >>= val op >>= = V.>>=
val ret = V.ret

fun ppM pp M = V.ppM "    " pp M

fun try_fun {name, f, arg, d} =
    let val () = print ("\nTrying example: " ^ name ^ "\n")
        val () = print ("  " ^ name ^ " = " ^ F.pp f ^ "\n")

        val () = print "  Differentiating:\n"
        val M = D.diffM nil f arg
        val () = print ("  f " ^ V.pp arg ^ " =\n" ^ ppM (fn (r,_) => V.pp r) M ^ "\n")

        val fM = M >>= (fn (_,l) => ret l)
        val () = print ("  f' " ^ V.pp arg ^ " =\n" ^ ppM L.pp fM ^ "\n")

        val fM = fM >>= (fn l => L.eval l d)
        val fM = V.simpl fM
        val () = print ("  f' " ^ V.pp arg ^ " " ^ V.pp d ^ " =\n" ^
                        ppM V.pp fM ^ "\n\n")
    in ()
    end

fun RVar s = V.Var s

local open F.DSL
      infix x nonfix + nonfix *
in

val Dot = F.Bilin Prim.Dprod
val Norm2Sq = F.Bilin Prim.Norm2Sq
infix vscale cross dot norm2sq
fun f vscale g = F.Bilin Prim.Sprod o (f x g) o dup
fun f cross g = F.Bilin Prim.Cprod3 o (f x g) o dup
fun f norm2sq g = F.Bilin Prim.Norm2Sq o (f x g) o dup
fun f dot g = Dot o (f x g) o dup
infix +
val op + = fn (f,g) => (op +) o (f x g) o dup
val K1 = F.K (V.R 1.0)
val norm = pow 0.5 o Dot o dup
val nrm = (pow ~1.0 o norm) vscale id
val () = try_fun {name="norm", f=norm,arg=RVar "x",d=RVar "dx1"}
val () = try_fun {name="norm", f=norm,arg=V.T[V.R 3.0,V.R 4.0],d=V.T[V.R 1.0,V.R 0.0]}
val () = try_fun {name="nrm", f=nrm,arg=RVar "x",d=RVar "dx1"}
val () = try_fun {name="nrm", f=nrm,arg=V.T[RVar "x1",RVar "x2",RVar "x3"],
                  d=V.T[RVar "dx1",RVar "dx2",RVar "dx3"]}
val () = try_fun {name="nrm", f=nrm,arg=V.T[V.R 2.0,V.R 3.0,V.R 5.0],
                  d=V.T[V.R 1.0,V.R 0.0,V.R 0.0]}

val rodriguez =
    let val pi_r = F.Prj (2,1)
        val pi_X = F.Prj (2,2)
    in ((cos o norm o pi_r) vscale pi_X) +
       ((sin o norm o pi_r) vscale ((nrm o pi_r) cross pi_X)) +
       ((K1 + (~ o cos o norm o pi_r)) vscale (((nrm o pi_r) dot (nrm o pi_r)) vscale pi_X))
    end

val r = V.T[V.R 1.0, V.R 2.6, V.R 3.0]
val X = V.T[V.R 10.0, V.R 20.6, V.R 30.0]
val () = try_fun {name="rodriguez", f=rodriguez,arg=V.T[RVar "r",RVar "X"],d=V.T[RVar "dr",RVar "dX"]}
val () = try_fun {name="rodriguez", f=rodriguez,arg=V.T[r,X],d=V.T[r,X]}

val p2e =
    let val pi_1 = F.Prj (3,1)
        val pi_2 = F.Prj (3,2)
        val pi_3 = F.Prj (3,3)
    in (pow ~1.0 o pi_3) vscale ((pi_1 x pi_2) o dup)
    end

val arg = V.T[V.R 6.0, V.R 12.0, V.R 3.0]
val () = try_fun {name="p2e", f=p2e,arg=arg,d=V.T[V.R 1.0,V.R 0.0,V.R 0.0]}

val distort =
    let val pi_1 = F.Prj (2,1)
        val pi_2 = F.Prj (2,2)
        val pi_k = F.Prj (2,1)
        val pi_X = F.Prj (2,2)
    in ((K1 + (Norm2Sq o pi_X) vscale (pi_1 o pi_k)) +
       ((pow 2.0 o Norm2Sq o pi_X) vscale (pi_2 o pi_k))) vscale pi_k
    end
val () = try_fun {name="distort", f=distort,
                  arg=V.T[V.T[V.R 2.0,V.R 3.0],V.T[V.R 8.0,V.R 9.0]],
                  d=V.T[V.T[V.R 2.0,V.R 3.0],V.T[V.R 8.0,V.R 9.0]]}

fun lrangle (f,g) = F.Comp(F.FProd[f,g],F.Dup 2)

val project (* -> R^2 *) =
    let val pi_r = F.Prj (6,1)    (* R^3 *)
        val pi_C = F.Prj (6,2)    (* R^3 *)
        val pi_f = F.Prj (6,3)    (* R   *)
        val pi_x0 = F.Prj (6,4)   (* R^2 *)
        val pi_k = F.Prj (6,5)    (* R^2 *)
        val pi_X = F.Prj (6,6)    (* R^3 *)
    in pi_f vscale (distort o lrangle (pi_k, p2e o rodriguez o lrangle (pi_r, pi_X + (~ o pi_C))))
       + pi_x0
    end

val r = V.T[V.R 2.0, V.R 3.0, V.R 8.0]
val C = V.T[V.R 1.0, V.R 2.0, V.R 6.0]
val f = V.R 3.0
val x0 = V.T[V.R 1.0, V.R 2.0]
val k = V.T[V.R 2.0, V.R 3.0]
val X = V.T[V.R 6.0, V.R 9.0, V.R 2.0]

val () = try_fun {name="project", f=project,
                  arg=V.T[r,C,f,x0,k,X],
                  d=V.T[r,C,f,x0,k,X]}

val residual (* -> R^2 *) =
    let val pi_w = F.Prj (3,1)    (* R *)
        val pi_m = F.Prj (3,2)    (* R^2 *)
        val pi_P = F.Prj (3,3)    (* R^3*R^3*R*R^2*R^2*R^3 *)
    in lrangle (pi_w vscale (pi_m + ~ o project o pi_P), K1 + ~ o pow 2.0 o pi_w)
    end

val P = V.T[r,C,f,x0,k,X]
val dP = V.T[r,C,f,x0,k,X]
val w = V.R 1.2
val m = V.T[V.R 1.0,V.R 2.0]

val dw = V.R 0.2
val dm = V.T[V.R 0.3,V.R 1.0]

val () = try_fun {name="residual", f=residual,
                  arg=V.T[w,m,P],
                  d=V.T[dw,dm,dP]}

end
