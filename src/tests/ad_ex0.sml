val () = print "****\n**** Ex0\n****\n"

functor Ex0(V:VAL) : sig end = struct
structure Ad = AD(V)
open Ad

fun pp_expected expected (sel: V.v*V.v->V.v) (v:V.v) : string =
    case expected of NONE => ""
                   | SOME p => if V.eq(v,sel p) then ": OK"
                               else (": WRONG - expected " ^ V.pp (sel p) ^ " - got " ^ V.pp v)

fun try_ex {name, e, par, arg, d, expected} =
    let val () = print ("Trying ex: " ^ name ^ "\n")
        val () = print ("  e = " ^ E.pp e ^ "\n")
        val f1 = E.trans par e
        val () = print ("  f_unopt = " ^ F.pp f1 ^ "\n")
        val f = F.opt f1
        val () = print ("  f = " ^ F.pp f ^ "\n")
        val e' = E.snart par f
        val () = print ("  e (from f) = " ^ E.pp e' ^ "\n")
        val (r,l) = D.diff nil f arg
        val () = print ("  f(" ^ V.pp arg ^ ") = " ^ V.pp r ^ pp_expected expected (#1) r ^ "\n")
        val () = print ("  f'(" ^ V.pp arg ^ ") = " ^ L.pp l ^ "\n")
        val rM = L.eval l d
        val () = print ("  f'(" ^ V.pp arg ^ ")(" ^ V.pp d ^ ") =\n" ^
                        V.ppM "    " V.pp rM ^ pp_expected expected (#2) (V.getVal rM) ^ "\n")
        val () = print "\n"
    in ()
    end

fun try_fun {name, f, arg, d, expected} =
    let val () = print ("Trying fun example: " ^ name ^ "\n")
        val () = print ("  f = " ^ F.pp f ^ "\n")
        val (r,l) = D.diff nil f arg
        val () = print ("  f(" ^ V.pp arg ^ ") = " ^ V.pp r ^ "\n")
        val () = print ("  f'(" ^ V.pp arg ^ ") = " ^ L.pp l ^ "\n")
        val rM = L.eval l d
        val () = print ("  f'(" ^ V.pp arg ^ ")(" ^ V.pp d ^ ") =\n" ^
                        V.ppM "    " V.pp rM ^ pp_expected expected (#2) (V.getVal rM) ^ "\n")
        val () = print "\n"
    in ()
    end

local open E.DSL
in
val () = try_ex {name="ex1", e=ln (sin x1), par=["x1"], arg=V.R 3.0, d=V.R 1.0,
                 expected=SOME(V.R ~1.95814462961,V.R ~7.01525255143)}
val () = try_ex {name="ex2", e=x1*x2, par=["x1","x2"], arg=V.T[V.R 3.0,V.R 1.0], d=V.T[V.R 1.0,V.R 0.0],
                 expected=SOME(V.R 3.0,V.R 1.0)}
val () = try_ex {name="ex3", e=ln x1 + x1*x2 - sin x2, par=["x1","x2"], arg=V.T[V.R 3.0,V.R 1.0], d=V.T[V.R 1.0,V.R 0.0],
                 expected=SOME(V.R 3.25714130386, V.R 1.33333333333)}
val () = try_ex {name="ex4", e=ln x1 + x1*x2 - sin x2, par=["x1","x2"], arg=V.T[V.R 3.0,V.R 1.0], d=V.T[V.R 0.0,V.R 1.0],
                 expected=SOME(V.R 3.25714130386, V.R 2.45969769413)}

val () = try_ex {name="ex5", e=lett ("x8", ln x1 + x1*x2, V "x8" - sin x2 + V "x8"), par=["x1","x2"], arg=V.T[V.R 3.0,V.R 1.0], d=V.T[V.R 0.0,V.R 1.0],
                 expected=SOME(V.R 7.35575359253, V.R 5.45969769413)}
end

local open F.DSL
      infix x nonfix + nonfix *
in
val () = try_fun {name="fun1", f=(id x ln) o dup o (+) o (cos x sin),arg=V.T[V.R 1.5,V.R 2.0],
                  d=V.T[V.R 2.0,V.R 2.0],
                  expected=SOME(V.T[V.R 0.980034628493,V.R ~0.0201673727445],
                                V.T[V.R ~2.8272836463,V.R ~2.8848813747])}
end
end

structure Ex0_Val = Ex0(Val)

structure Ex0_TermVal = Ex0(TermVal)
