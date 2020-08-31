val () = print "****\n**** Ex1\n****\n"
structure Ad = AD(TermVal)
open Ad
structure V = TermVal

fun try_ex {name, e, arg, dx, dy} =
    let val () = print ("Trying example: " ^ name ^ "\n")
        val () = print ("  e = " ^ E.pp e ^ "\n")
        val f1 = E.trans e
        val () = print ("  f_unopt = " ^ F.pp f1 ^ "\n")
        val f = F.opt f1
        val () = print ("  f = " ^ F.pp f ^ "\n")
        val (r,l) = D.diff f arg
        val () = print ("  f " ^ V.pp arg ^ " = " ^ V.pp r ^ "\n")
        val () = print ("  f' " ^ V.pp arg ^ " = " ^ L.pp l ^ "\n")
        val rM = L.eval l dx
        val rM = V.simpl rM
        val () = print ("  f' " ^ V.pp arg ^ " " ^ V.pp dx ^ " =\n" ^
                        V.ppM "    " V.pp rM ^ "\n")
    in ()
    end

fun try_fun {name, f, arg, d} =
    let val () = print ("Trying example: " ^ name ^ "\n")
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
        val () = print "\n"
    in ()
    end

local open E.DSL
in
val () = try_ex {name="t1", e=ln (sin x1), arg=V.T[V.Var "x1"], dx=V.T[V.R 1.0],
                 dy=V.T[V.Var "dy1"]}
val () = try_ex {name="t2", e=x1*x2, arg=V.T[V.Var "x1",V.Var "x2"], dx=V.T[V.R 1.0,V.R 0.0],
                 dy=V.T[V.Var "dy1"]}
val () = try_ex {name="t3", e=ln x1 + x1*x2 - sin x2, arg=V.T[V.Var "x1",V.Var "x2"],
                 dx=V.T[V.R 1.0,V.R 0.0], dy=V.T[V.Var "dy1"]}
val () = try_ex {name="t4", e=ln x1 + x1*x2 - sin x2, arg=V.T[V.Var "x1",V.Var "x2"],
                 dx=V.T[V.Var "dx1",V.Var "dx2"],dy=V.T[V.Var "dy1"]}
val () = try_ex {name="t4'", e=ln x1 + (x1*x2 - sin x2), arg=V.T[V.Var "x1",V.Var "x2"],
                 dx=V.T[V.Var "dx1",V.Var "dx2"],dy=V.T[V.Var "dy1"]}
val () = try_ex {name="t5", e= ~ (sin x1), arg=V.T[V.Var "x1"], dx=V.T[V.Var "dx1"],
                 dy=V.T[V.Var "dy1"]}
end

local open F.DSL
      infix x nonfix + nonfix *
in
val () = try_fun {name="fun1", f=(id x ln) o dup o (+) o (cos x sin),arg=V.T[V.Var "x1",V.Var "x2"],
                  d=V.T[V.R 2.0,V.R 2.0]}
                 (* f'((x1,x2)) = (id :+: (pow(~1.0)((cos(x1) + sin(x2)))* )) :o:
                    dup :o: (+) :o: ((sin(x1)* ) :+: (~(cos(x2))* )) *)
val () = try_fun {name="fun2", f=ln,arg=V.T[V.Var "x1"],d=V.T[V.R 2.0]}

end
