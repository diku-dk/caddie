val () = print "****\n**** Reverse AD Ex0\n****\n"

functor Ex0(V:VAL) : sig end = struct
structure Ad = AD(V)
open Ad

fun pp_expected expected (sel: V.v*V.v->V.v) (v:V.v) : string =
    case expected of NONE => ""
                   | SOME p => if V.eq(v,sel p) then ": OK"
                               else (": WRONG - expected " ^ V.pp (sel p) ^ " - got " ^ V.pp v)

fun ex {name, e, par, arg, d, expected} =
    let val () = print ("Trying ex: " ^ name ^ "\n")
        val () = print ("  e = " ^ E.pp e ^ "\n")
        val f1 = E.trans par e
        val () = print ("  f_unopt = " ^ F.pp f1 ^ "\n")
        val f = F.opt f1
        val () = print ("  f = " ^ F.pp f ^ "\n")
        val e' = E.snart par f
        val () = print ("  e (from f) = " ^ E.pp e' ^ "\n")
        val (r,l) = D.diff nil f arg
        val l = L.adjoint l
        val () = print ("  f(" ^ V.pp arg ^ ") = " ^ V.pp r ^ pp_expected expected (#1) r ^ "\n")
        val () = print ("  f'(" ^ V.pp arg ^ ") = " ^ L.pp l ^ "\n")
        val () = print "Now evaluating\n"
        val rM = L.eval l d
        val () = print ("  f'(" ^ V.pp arg ^ ")(" ^ V.pp d ^ ") =\n" ^
                        V.ppM "    " V.pp rM ^ "\n")
        val () = print (pp_expected expected (#2) (V.getVal rM) ^ "\n")
        val () = print "\n"
    in ()
    end


local open E.DSL
in
val () = ex {name="ex1", e=ln (sin x1), par=["x1"], arg=V.R 3.0, d=V.R 1.0,
             expected=SOME(V.R ~1.95814462961,V.R ~7.01525255143)}

val () = ex {name="ex2", e=x1*x2, par=["x1","x2"], arg=V.T[V.R 3.0,V.R 1.0], d=V.R 1.0,
             expected=SOME(V.R 3.0, V.T[V.R 1.0,V.R 3.0])}

val () = ex {name="ex3", e=ln x1 + x1*x2 - sin x2, par=["x1","x2"], arg=V.T[V.R 3.0,V.R 1.0], d=V.R 1.0,
             expected=SOME(V.R 3.25714130386, V.T[V.R 1.33333333333,V.R 2.45969769413])}

end
end

(*structure Ex0_Val = Ex0(Val)*)

structure Ex0_TermVal = Ex0(TermVal)
