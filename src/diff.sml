functor Diff(V:VAL) : DIFF where type v = V.v = struct
structure F = Fun(V)
structure L = Lin(V)
type v = V.v

fun diff (f:F.f) (x:v) : v * L.lin =
    case f of
        F.Comp(g,f) =>                   (* g o f *)
        let val (fx,f'x) = diff f x
            val (gfx,g'fx) = diff g fx
        in (gfx,L.comp(g'fx,f'x))
        end
      | F.K y => (y, L.zero)
      | F.Add =>
        let val h = V.add
        in (h x, L.lin("add",h))
        end
      | F.Uprim Prim.Neg =>
        let val h = V.uprim Prim.Neg
        in (h x,
            L.lin("neg",h))
        end
      | F.Uprim p => (V.uprim p x,
                      L.curL (Prim.Mul,V.uprim_diff p x))
      | F.Prj i =>
        let val h = V.prjI ("Prj" ^ Int.toString i) i
        in (h x, L.prj i)
        end
      | F.Dup =>
        let val h = fn v => V.T[v,v]
        in (h x, L.lin("dup",h))
        end
      | F.FProd(f,g) =>
        let val (fx,f'x) = diff f (V.prjI "fprod-x" 1 x)
            val (gy,g'y) = diff g (V.prjI "fprod-y" 2 x)
        in (V.T[fx,gy],L.oplus(f'x,g'y))
        end
      | F.Bilin p =>
        (V.bilin (p,x),
         L.comp(L.lin ("add",V.add),
                L.oplus(L.curR(p,V.prjI "mul-R" 2 x),
                        L.curL(p,V.prjI "mul-L" 1 x))))
      | F.Id => (x, L.id)
end
