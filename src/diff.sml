functor Diff(V:VAL) : DIFF where type v = V.v = struct

structure F = Fun(V)
structure L = Lin(V)

fun die s = (print ("Error (Diff): " ^ s ^ "\n"); raise Fail s)

type v = V.v

fun diff (f:F.f) (x:v) : v * L.lin =
    case f of
        F.Comp(g,f) =>                   (* g o f *)
        let val (fx,f'x) = diff f x
            val (gfx,g'fx) = diff g fx
        in (gfx,L.comp(g'fx,f'x))
        end
      | F.K y => (y, L.zero)
      | F.Add => (V.add x, L.add)
      | F.Uprim Prim.Neg => (V.uprim Prim.Neg x, L.neg)
      | F.Uprim p => (V.uprim p x,
                      L.curL (Prim.Mul,V.uprim_diff p x))
      | F.Prj (1,i) => (x,L.id)                                  (*ok*)
      | F.Prj (d,i) => (V.prjI ("Prj" ^ Int.toString i ^ "/" ^ Int.toString d) i x, L.prj d i)
      | F.Dup => (V.T[x,x], L.dup)
      | F.FProd(f,g) =>
        let val (fx,f'x) = diff f (V.prjI "fprod-x" 1 x)
            val (gy,g'y) = diff g (V.prjI "fprod-y" 2 x)
        in (V.T[fx,gy],L.oplus(f'x,g'y))
        end
      | F.Bilin p =>
        (V.bilin (p,x),
         L.comp(L.add,
                L.oplus(L.curR(p,V.prjI "mul-R" 2 x),
                        L.curL(p,V.prjI "mul-L" 1 x))))
      | F.Id => (x, L.id)
      | F.If _ => die "diff - If not supported"

type 'a M = 'a V.M
val op >>= = V.>>= infix >>=
val ret = V.ret

fun diffM (f:F.f) (x:v) : (v * L.lin) M =
    case f of
        F.Comp(g,f) =>                   (* g o f *)
        diffM f x >>= (fn (fx,f'x) =>
        diffM g fx >>= (fn (gfx,g'fx) =>
        ret (gfx,L.comp(g'fx,f'x))))
      | F.K y => ret (y, L.zero)
      | F.Add => ret (V.add x, L.add)
      | F.Uprim Prim.Neg => ret (V.uprim Prim.Neg x, L.neg)
      | F.Uprim p => ret (V.uprim p x,
                          L.curL (Prim.Mul,V.uprim_diff p x))
      | F.Prj (1,i) => ret (x,L.id)                                  (*ok*)
      | F.Prj (d,i) => ret (V.prjI ("Prj" ^ Int.toString i ^ "/" ^ Int.toString d) i x, L.prj d i)
      | F.Dup => V.letBind x >>= (fn x => ret (V.T[x,x], L.dup))
      | F.FProd(f,g) =>
        diffM f (V.prjI "fprod-x" 1 x) >>= (fn (fx,f'x) =>
        diffM g (V.prjI "fprod-y" 2 x) >>= (fn (gy,g'y) =>
        ret (V.T[fx,gy],L.oplus(f'x,g'y))))
      | F.Bilin p =>
        (case V.unT x of
             SOME [x1,x2] =>
             V.letBind x1 >>= (fn x1 =>
             V.letBind x2 >>= (fn x2 =>
             ret (V.bilin (p,V.T[x1,x2]),
                  L.comp(L.add,
                         L.oplus(L.curR(p,x2),
                                 L.curL(p,x1))))))
           | _ => die "diffM: expecting pair in Bilin")
      | F.Id => ret (x, L.id)
      | F.If(f,g,h) =>
        diffM f x >>= (fn (fx,_) =>
        let val mg = diffM g x
            val mh = diffM h x
        in ret(V.iff(fx, mg >>= (ret o #1), mh >>= (ret o #1)),
               L.iff(fx, mg >>= (ret o #2), mh >>= (ret o #2)))
        end)

(*
fun diffr (f:F.f) (x:v) : v * L.lin =
    case f of
        F.Comp(g,f) =>                                           (*ok*)
        let val (fx,f'x) = diffr f x
            val (gfx,g'fx) = diffr g fx
        in (gfx,L.comp(f'x,g'fx))
        end
      | F.K y => (y, L.zero)                                     (*ok*)
      | F.Add => (V.add x, L.dup)                                (*ok*)
      | F.Uprim Prim.Neg => (V.uprim Prim.Neg x, L.neg)          (*ok*)
      | F.Uprim p => (V.uprim p x,
                      L.curL (Prim.Mul,V.uprim_diff p x))
      | F.Prj (1,i) => (x,L.id)                                  (*ok*)
      | F.Prj (2,i) =>                                           (*ok*)
        let val l = case i of
                        1 => L.oplus(L.id,L.zero)
                      | 2 => L.oplus(L.zero,L.id)
                      | _ => die ("non-supported projection "^Int.toString i ^ "/2")
        in (V.prjI ("Prj" ^ Int.toString i) i x,
            l)
        end
      | F.Prj (d,i) =>
        die ("non-supported projection "^Int.toString i ^ "/" ^ Int.toString d)
      | F.Dup => (V.T[x,x], L.add)                               (*ok*)
      | F.FProd(f,g) =>
        let val (fx,f'x) = diff f (V.prjI "fprod-x" 1 x)
            val (gy,g'y) = diff g (V.prjI "fprod-y" 2 x)
        in (V.T[fx,gy],L.oplus(f'x,g'y))
        end
      | F.Bilin p =>                                             (*ok*)
        (V.bilin (p,x),
         L.comp(L.oplus(L.transp(L.curR(p,V.prjI "bilin-R" 2 x)),
                        L.transp(L.curL(p,V.prjI "bilin-L" 1 x))),
                L.dup))
      | F.Id => (x, L.id)
*)

end
