val () = print "****\n**** Reverse AD Ex1\n****\n"
structure Ad = AD(TermVal)
open Ad
structure V = TermVal

infix >>= val op >>= = V.>>=
val ret = V.ret

fun ppM pp M = V.ppM "    " pp M

fun ex {name, e, par, arg, dy} =
    let val () = print ("Trying example: " ^ name ^ "\n")
        val () = print ("  e = " ^ E.pp e ^ "\n")

        val f1 = E.trans par e
        val () = print ("  f_unopt = " ^ F.pp f1 ^ "\n")

        val f = F.opt f1
        val () = print ("  f = " ^ F.pp f ^ "\n")

        val () = print "  Differentiating:\n"
        val M = D.diffM nil f arg
        val () = print ("  f " ^ V.pp arg ^ " =\n" ^ ppM (fn (r,_) => V.pp r) M ^ "\n")

        val fM = M >>= (fn (_,l) => ret l)
        val () = print ("  f' " ^ V.pp arg ^ " =\n" ^ ppM L.pp fM ^ "\n")

        val rM = fM >>= (ret o L.adjoint)
        val () = print ("  f^ " ^ V.pp arg ^ " =\n" ^ ppM L.pp rM ^ "\n")

        val gM = rM >>= (fn l => L.eval l dy)
        val gM = V.simpl gM
        val () = print ("  f^ " ^ V.pp arg ^ " " ^ V.pp dy ^ " =\n" ^
                        ppM V.pp gM ^ "\n\n")
    in ()
    end

local open E.DSL
in
val () = ex {name="ex1", e= ln (sin x1), par=["x1"], arg=V.Var "x1", dy=V.R 1.0}

val () = ex {name="ex2", e= x1*x2, par=["x1","x2"], arg=V.T[V.Var "x1",V.Var "x2"], dy=V.R 1.0}

val () = ex {name="ex3", e= ln x1 + x1*x2 - sin x2, par=["x1","x2"], arg=V.T[V.Var "x1",V.Var "x2"], dy=V.R 1.0}

val () = ex {name="ex4", arg=V.T[V.Var "x1",V.Var "x2"], dy=V.R 1.0,
             e= (ln x1 + x1*x2 - sin x2) * (x1 + x2), par=["x1","x2"]
            }

val () = ex {name="ex5", arg=V.T[V.Var "x1",V.Var "x2"], dy=V.R 1.0,
             e= ln (x1 * cos x2), par=["x1","x2"]
            }

val () = ex {name="ex6", arg=V.T[V.Var "x1",V.Var "x2"], dy=V.R 1.0,
             e=  x2*(~(iff(x1,x2*x1,sin x2))), par=["x1","x2"]
            }

end
