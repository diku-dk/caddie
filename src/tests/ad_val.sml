(* Dynamically tagged version of combinatory differentiation interpretation (in SML)
 *
 * Todo:
 *  1) More examples
 *  2) Experiment with forward/reverse mode differences
 *
 * Questions:
 *  1) Can we somehow convert point-free notation to expressions with let-expressions?
 *)


functor Ex0(V:VAL) : sig end = struct
structure D = Diff(V)
structure F = D.F
structure E = Exp(structure V = V
                  structure F = F)
structure L = D.L

fun pp_expected expected (sel: V.v*V.v->V.v) (v:V.v) : string =
    case expected of NONE => ""
                   | SOME p => if V.eq(v,sel p) then ": OK"
                               else (": WRONG - expected " ^ V.pp v ^ " - got " ^ V.pp (sel p))

fun try_ex {name, e, arg, d, expected} =
    let val () = print ("\n\nTrying ex: " ^ name ^ "\n")
        val () = print ("  e = " ^ E.pp e ^ "\n")
        val f1 = E.trans e
        val () = print ("  f_unopt = " ^ F.pp f1 ^ "\n")
        val f = F.opt f1
        val () = print ("  f = " ^ F.pp f ^ "\n")
        val e' = E.snart f
        val () = print ("  e' = " ^ E.pp e' ^ "\n")
        val (r,l) = D.diff f arg
        val () = print ("  f(" ^ V.pp arg ^ ") = " ^ V.pp r ^ pp_expected expected (#1) r ^ "\n")
        val () = print ("  f'(" ^ V.pp arg ^ ") = " ^ L.pp l ^ "\n")
        val rM = L.eval l d
        val () = print ("  f'(" ^ V.pp arg ^ ")(" ^ V.pp d ^ ") =\n" ^
                        V.ppM "    " V.pp rM ^ pp_expected expected (#2) (V.getVal rM) ^ "\n")
    in ()
    end

fun try_fun {name, f, arg, d, expected} =
    let val () = print ("\n\nTrying fun example: " ^ name ^ "\n")
        val () = print ("  f = " ^ F.pp f ^ "\n")
        val (r,l) = D.diff f arg
        val () = print ("  f(" ^ V.pp arg ^ ") = " ^ V.pp r ^ "\n")
        val () = print ("  f'(" ^ V.pp arg ^ ") = " ^ L.pp l ^ "\n")
        val rM = L.eval l d
        val () = print ("  f'(" ^ V.pp arg ^ ")(" ^ V.pp d ^ ") =\n" ^
                        V.ppM "    " V.pp rM ^ pp_expected expected (#2) (V.getVal rM) ^ "\n")
    in ()
    end

local open E.DSL
in
val () = try_ex {name="ex1", e=ln (sin x1), arg=V.T[V.R 3.0], d=V.T[V.R 1.0],expected=SOME(V.R ~1.95814462961,V.R 7.01525255143)}
val () = try_ex {name="ex2", e=x1*x2, arg=V.T[V.R 3.0,V.R 1.0], d=V.T[V.R 1.0,V.R 0.0],expected=SOME(V.R 3.0,V.R 1.0)}
val () = try_ex {name="ex3", e=ln x1 + x1*x2 - sin x2, arg=V.T[V.R 3.0,V.R 1.0], d=V.T[V.R 1.0,V.R 0.0],expected=SOME(V.R 3.25714130386, V.R 1.33333333333)}
end

local open F.DSL
      infix x nonfix + nonfix *
in
val () = try_fun {name="fun1", f=(id x ln) o dup o (+) o (cos x sin),arg=V.T[V.R 1.5,V.R 2.0],d=V.T[V.R 2.0,V.R 2.0],
                  expected=SOME(V.T[V.R 0.980034628493,V.R ~0.0201673727445],
                                V.T[V.R 2.8272836463,V.R 2.8848813747])}
end
end

structure Ex0_Val = Ex0(Val)

structure Ex0_TermVal = Ex0(TermVal)

functor Ex1() : sig end = struct

val () = print "****\n**** Ex1\n****\n"
structure V = TermVal
structure D = Diff(V)
structure F = D.F
structure E = Exp(structure V = V
                  structure F = F)
structure L = D.L

fun try_ex {name, e, arg, d} =
    let val () = print ("\nTrying example: " ^ name ^ "\n")
        val () = print ("  e = " ^ E.pp e ^ "\n")
        val f1 = E.trans e
        val () = print ("  f_unopt = " ^ F.pp f1 ^ "\n")
        val f = F.opt f1
        val () = print ("  f = " ^ F.pp f ^ "\n")
        val (r,l) = D.diff f arg
        val () = print ("  f " ^ V.pp arg ^ " = " ^ V.pp r ^ "\n")
        val () = print ("  f' " ^ V.pp arg ^ " = " ^ L.pp l ^ "\n")
        val rM = L.eval l d
        val rM = V.simpl rM
        val () = print ("  f' " ^ V.pp arg ^ " " ^ V.pp d ^ " =\n" ^
                        V.ppM "    " V.pp rM ^ "\n")
    in ()
    end

fun try_fun {name, f, arg, d} =
    let val () = print ("\nTrying example: " ^ name ^ "\n")
        val () = print ("  " ^ name ^ " = " ^ F.pp f ^ "\n")
        val (r,l) = D.diff f arg
        val () = print ("  " ^ name ^ " " ^ V.pp arg ^ " = " ^ V.pp r ^ "\n")
        val () = print ("  " ^ name ^ "' " ^ V.pp arg ^ " = " ^ L.pp l ^ "\n")
        val () = print "Now evaluating\n"
        val rM = L.eval l d
        val () = print "Now simplifying\n"
        val rM = V.simpl rM
        val () = print ("  " ^ name ^ "' " ^ V.pp arg ^ " " ^ V.pp d ^ " =\n" ^
                        V.ppM "    " V.pp rM ^ "\n")
    in ()
    end

local open E.DSL
in
val () = try_ex {name="t1", e=ln (sin x1), arg=V.T[V.Var "x1"], d=V.T[V.R 1.0]}
val () = try_ex {name="t2", e=x1*x2, arg=V.T[V.Var "x1",V.Var "x2"], d=V.T[V.R 1.0,V.R 0.0]}
val () = try_ex {name="t3", e=ln x1 + x1*x2 - sin x2, arg=V.T[V.Var "x1",V.Var "x2"], d=V.T[V.R 1.0,V.R 0.0]}
val () = try_ex {name="t4", e=ln x1 + x1*x2 - sin x2, arg=V.T[V.Var "x1",V.Var "x2"], d=V.T[V.Var "dx1",V.Var "dx2"]}
val () = try_ex {name="t4'", e=ln x1 + (x1*x2 - sin x2), arg=V.T[V.Var "x1",V.Var "x2"], d=V.T[V.Var "dx1",V.Var "dx2"]}
val () = try_ex {name="t5", e= ~ (sin x1), arg=V.T[V.Var "x1"], d=V.T[V.Var "dx1"]}
end

local open F.DSL
      infix x nonfix + nonfix *
in
val () = try_fun {name="fun1", f=(id x ln) o dup o (+) o (cos x sin),arg=V.T[V.Var "x1",V.Var "x2"],d=V.T[V.R 2.0,V.R 2.0]}
                 (* f'((x1,x2)) = (id :+: (pow(~1.0)((cos(x1) + sin(x2)))* )) :o: dup :o: (+) :o: ((sin(x1)* ) :+: (~(cos(x2))* )) *)
val () = try_fun {name="fun2", f=ln,arg=V.T[V.Var "x1"],d=V.T[V.R 2.0]}

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
val () = try_fun {name="norm", f=norm,arg=V.Var "x",d=V.Var "dx1"}
val () = try_fun {name="norm", f=norm,arg=V.T[V.R 3.0,V.R 4.0],d=V.T[V.R 1.0,V.R 0.0]}
val () = try_fun {name="nrm", f=nrm,arg=V.Var "x",d=V.Var "dx1"}
val () = try_fun {name="nrm", f=nrm,arg=V.T[V.Var "x1",V.Var "x2",V.Var "x3"],
                  d=V.T[V.Var "dx1",V.Var "dx2",V.Var "dx3"]}
val () = try_fun {name="nrm", f=nrm,arg=V.T[V.R 2.0,V.R 3.0,V.R 5.0],
                  d=V.T[V.R 1.0,V.R 0.0,V.R 0.0]}

val rodriguez =
    let val pi_r = F.Prj 1
        val pi_X = F.Prj 2
    in ((cos o norm o pi_r) vscale pi_X) +
       ((sin o norm o pi_r) vscale ((nrm o pi_r) cross pi_X)) +
       ((K1 + (~ o cos o norm o pi_r)) vscale (((nrm o pi_r) dot (nrm o pi_r)) vscale pi_X))
    end

val r = V.T[V.R 1.0, V.R 2.6, V.R 3.0]
val X = V.T[V.R 10.0, V.R 20.6, V.R 30.0]
val () = try_fun {name="rodriguez", f=rodriguez,arg=V.T[V.Var "r",V.Var "X"],d=V.T[V.Var "dr",V.Var "dX"]}
val () = try_fun {name="rodriguez", f=rodriguez,arg=V.T[r,X],d=V.T[r,X]}

val p2e =
    let val pi_1 = F.Prj 1
        val pi_2 = F.Prj 2
        val pi_3 = F.Prj 3
    in (pow ~1.0 o pi_3) vscale ((pi_1 x pi_2) o dup)
    end

val arg = V.T[V.R 6.0, V.R 12.0, V.R 3.0]
val () = try_fun {name="p2e", f=p2e,arg=arg,d=V.T[V.R 1.0,V.R 0.0,V.R 0.0]}

val distort =
    let val pi_1 = F.Prj 1
        val pi_2 = F.Prj 2
        val pi_k = F.Prj 1
        val pi_X = F.Prj 2
    in ((K1 + (Norm2Sq o pi_X) vscale (pi_1 o pi_k)) +
       ((pow 2.0 o Norm2Sq o pi_X) vscale (pi_2 o pi_k))) vscale pi_k
    end
val () = try_fun {name="distort", f=distort,
                  arg=V.T[V.T[V.R 2.0,V.R 3.0],V.T[V.R 8.0,V.R 9.0]],
                  d=V.T[V.T[V.R 2.0,V.R 3.0],V.T[V.R 8.0,V.R 9.0]]}

fun lrangle (f,g) = F.Comp(F.FProd(f,g),F.Dup)

val project (* -> R^2 *) =
    let val pi_r = F.Prj 1    (* R^3 *)
        val pi_C = F.Prj 2    (* R^3 *)
        val pi_f = F.Prj 3    (* R   *)
        val pi_x0 = F.Prj 4   (* R^2 *)
        val pi_k = F.Prj 5    (* R^2 *)
        val pi_X = F.Prj 6    (* R^3 *)
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
    let val pi_w = F.Prj 1    (* R *)
        val pi_m = F.Prj 2    (* R^2 *)
        val pi_P = F.Prj 3    (* R^3*R^3*R*R^2*R^2*R^3 *)
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

end

structure X = Ex1()
