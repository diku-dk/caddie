structure Main = struct

structure A = Ast

val s = "10*let   y=82+2 in let x =454\nin y+(x-y) (* ok *)\n + 23 end end" (* 4770 *)
val s1 = "3+2*5-3*2"    (* 7 *)
val s2 = "3*2+2*10*2+6" (* 52 *)
val s3 = "10-2-3-1"     (* 4 *)
val s4 = "abs (10-23)"  (* 13 *)
val s5 = "(10,20+30*2)" (* (10,80) *)
val s6 = "2+ #2(10,20+30*2)" (* 80 *)
val s7 = "iota 3" (* [0, 1, 2] *)
val s8 = "map (fn x => x * 3) (map (fn x => x + 2) (iota 3))"

val e = A.parse {srcname="stdin",input=s8}

val v = A.eval (fn x => x) A.VEinit e

val () = print ("Eval = " ^ A.pr_v v ^ " : " ^ A.pr_ty(#2(A.tyinf_exp A.TEinit e)) ^ "\n")

val sp1 = "fun f x = (2 * x, 3 - x) fun g y = (f y, f (2*y))"
val sp2 = "fun f x = 22"

val p = A.parse_prg {srcname="stdin",input=sp1}

val v = A.eval_prg (fn x => x) p "g" (A.real_v 4.0)

val () = print ("Eval = " ^ A.pr_v v ^ "\n")

end
