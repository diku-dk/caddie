functor Diff(V:VAL) : DIFF where type v = V.v = struct

structure F = Fun(V)
structure L = Lin(V)

fun mapi f xs =
    let fun loop n nil = nil
          | loop n (x::xs) = f(x,n) :: loop (n+1) xs
    in loop 0 xs
    end

fun die s = (print ("Error (Diff): " ^ s ^ "\n"); raise Fail s)

type v = V.v

type env = (string * F.f) list

fun look E n =
    case E of
        (k,v)::rest => if n=k then SOME v
                       else look rest n
      | _ => NONE

fun diff (E:env) (f:F.f) (x:v) : v * L.lin =
    let fun D f x =
            case f of
                F.Comp(g,f) =>                   (* g o f *)
                let val (fx,f'x) = D f x
                    val (gfx,g'fx) = D g fx
                in (gfx,L.comp(g'fx,f'x))
                end
              | F.K y => (y, L.zero)
              | F.Add => (V.add x, L.add 2)
              | F.Uprim Prim.Neg => (V.uprim Prim.Neg x, L.neg)
              | F.Uprim p => (V.uprim p x,
                              L.curL (Prim.Mul,V.uprim_diff p x))
              | F.Prj (1,i) => (x,L.id)                                  (*ok*)
              | F.Prj (d,i) => (V.prjI ("Prj" ^ Int.toString i ^ "/" ^ Int.toString d) i x, L.prj d i)
              | F.Dup n => (V.T(List.tabulate(n,fn _=> x)), L.dup n)
              | F.FProd fs =>
                let val pairs = mapi (fn (f,i) => D f (V.prjI "fprod-x" (i+1) x)) fs
                    val (fxs,f'xs) = ListPair.unzip pairs
                in (V.T fxs,L.oplus f'xs)
                end
              | F.Bilin p =>
                (V.bilin (p,x),
                 L.comp(L.add 2,
                        L.oplus[L.curR(p,V.prjI "mul-R" 2 x),
                                L.curL(p,V.prjI "mul-L" 1 x)]))
              | F.Id => (x, L.id)
              | F.If _ => die "diff - If not supported"
              | F.NamedFun n =>
                (case look E n of
                     SOME f => D f x
                   | NONE => die ("diff: unknown function " ^ n))
              | F.Map f  =>
                 let val fvs = V.map (#1 o D f) x
                     val linp =  V.mk_f (#2 o D f)
                 in (fvs, L.lmapP (V.ret linp, x))
                 end
              | F.Red r => (V.red r x, L.red r)
    in D f x
    end
and eval (E:env) (f:F.f) = #1 o diff E f

type 'a M = 'a V.M
val op >>= = V.>>= infix >>=
val ret = V.ret

fun diffM (E:env) (f:F.f) (x:v) : (v * L.lin) M =
    let fun D f x =
            case f of
                F.Comp(g,f) =>                   (* g o f *)
                  D f x >>= (fn (fx,f'x) =>
                  D g fx >>= (fn (gfx,g'fx) =>
                  ret (gfx,L.comp(g'fx,f'x))))
              | F.K y => ret (y, L.zero)
              | F.Add => ret (V.add x, L.add 2)
              | F.Uprim Prim.Neg => ret (V.uprim Prim.Neg x, L.neg)
              | F.Uprim p => ret (V.uprim p x,
                                  L.curL (Prim.Mul,V.uprim_diff p x))
              | F.Prj (1,i) => ret (x,L.id)                                  (*ok*)
              | F.Prj (d,i) => ret (V.prjI ("Prj" ^ Int.toString i ^ "/" ^ Int.toString d) i x, L.prj d i)
              | F.Dup n => V.letBind x >>= (fn x => ret (V.T(List.tabulate(n,fn _=> x)), L.dup n))
              | F.FProd fs =>
                Ds fs (List.tabulate(length fs, fn i => V.prjI "fprod-x" (i+1) x)) >>= (fn (fxs,f'xs) =>
                ret (V.T fxs,L.oplus f'xs))
              | F.Bilin p =>
                (case V.unT x of
                     SOME [x1,x2] =>
                     V.letBind x1 >>= (fn x1 =>
                     V.letBind x2 >>= (fn x2 =>
                     ret (V.bilin (p,V.T[x1,x2]),
                          L.comp(L.add 2,
                                 L.oplus[L.curR(p,x2),
                                         L.curL(p,x1)]))))
                   | _ => die "diffM: expecting pair in Bilin")
              | F.Id => ret (x, L.id)
              | F.If(f,g,h) =>
                D f x >>= (fn (fx,_) =>
                              let val mg = D g x
                                  val mh = D h x
                              in ret(V.iff(fx, mg >>= (ret o #1), mh >>= (ret o #1)),
                                     L.iff(fx, mg >>= (ret o #2), mh >>= (ret o #2)))
                              end)
              | F.NamedFun n =>
                (case look E n of
                     SOME f => D f x
                   | NONE => die ("diffM: unknown function " ^ n))
              | F.Map f  =>
                 let val fvs = V.mapM (fn x' => V.fmap #1 (D f x')) x
                     val linpM =  V.mk_fM (fn v => V.fmap #2 (D f v))
                 in ret (fvs, L.lmapP (linpM, x))
                 end
              | F.Red r => ret (V.red r x, L.red r)
        and Ds fs xs =
            case (fs,xs) of
                (nil,nil) => ret (nil,nil)
              | (f::fs,x::xs) => D f x >>= (fn (fx,f'x) =>
                                 Ds fs xs >>= (fn (fxs, f'xs) =>
                                 ret (fx::fxs, f'x::f'xs)))
              | _ => die "diffM.Ds.unmatching number of functions and arguments"
    in D f x
    end

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
