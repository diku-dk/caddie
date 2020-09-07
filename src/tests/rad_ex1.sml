val () = print "****\n**** Reverse AD Ex1\n****\n"
structure Ad = AD(TermVal)
open Ad
structure V = TermVal

fun ex {name, e, arg, dy} =
    let val () = print ("Trying example: " ^ name ^ "\n")
        val () = print ("  e = " ^ E.pp e ^ "\n")
        val f1 = E.trans e
        val () = print ("  f_unopt = " ^ F.pp f1 ^ "\n")
        val f = F.opt f1
        val () = print ("  f = " ^ F.pp f ^ "\n")
        val (r,l) = D.diff f arg
        val l = L.transp l
        val () = print ("  f " ^ V.pp arg ^ " = " ^ V.pp r ^ "\n")
        val () = print ("  f_nabla " ^ V.pp arg ^ " = " ^ L.pp l ^ "\n")
        val () = print "Now evaluating\n"
        val rM = L.eval l dy
        val () = print "Now simplifying\n"
        val rM = V.simpl rM
        val () = print ("  f_nabla " ^ V.pp arg ^ " " ^ V.pp dy ^ " =\n" ^
                        V.ppM "    " V.pp rM ^ "\n\n")
    in ()
    end

local open E.DSL
in
val () = ex {name="ex1", e=ln (sin x1), arg=V.Var "x1", dy=V.R 1.0}

val () = ex {name="ex2", e=x1*x2, arg=V.T[V.Var "x1",V.Var "x2"], dy=V.R 1.0}

val () = ex {name="ex3", e=ln x1 + x1*x2 - sin x2, arg=V.T[V.Var "x1",V.Var "x2"], dy=V.R 1.0}
end
