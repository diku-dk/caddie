(* Some utility functions *)

fun println s = print (s ^ "\n")

fun mapi f xs =
    let fun loop n nil = nil
          | loop n (x::xs) = f(x,n) :: loop (n+1) xs
    in loop 0 xs
    end

fun readFile f =
    let val is = TextIO.openIn f
    in let val c = TextIO.inputAll is
       in TextIO.closeIn is
        ; SOME c
       end handle _ => (TextIO.closeIn is; NONE)
    end handle _ => NONE

fun dieReg r s =
    raise Fail (Region.pp r ^ ": " ^ s)

(* Option specifications *)

val rad_p = CmdArgs.addFlag ("r", SOME ["Apply reverse mode AD."])

val verbose_p = CmdArgs.addFlag ("-verbose", SOME ["Be verbose."])

val exp_str = CmdArgs.addString ("e", "", SOME ["Expression to be evaluated after loading of program files."])

val () = CmdArgs.addUsage ("-help", "options... file1.cad ... fileN.cad")

val () = CmdArgs.addVersion ("-version", "Combinatory AD (CAD) v0.0.1")

val print_typed_p = CmdArgs.addFlag ("-Ptyped", SOME ["Print program after type inference."])
val print_exp_p = CmdArgs.addFlag ("-Pexp", SOME ["Print internal expression program."])
val print_pointfree_p = CmdArgs.addFlag ("-Ppointfree", SOME ["Print point free internal expression program."])
val print_diff_p = CmdArgs.addFlag ("-Pdiff", SOME ["Print differentiated program."])
val print_diff_unlinearised_p = CmdArgs.addFlag ("-Pdiffu", SOME ["Print unlinearised differentiated program."])

val srcs = CmdArgs.processOptions()

fun debug s =
    if verbose_p() then println ("[" ^ s ^ "]")
    else ()

(* Parsing and possibly evaluation *)

fun parse f =
    ( debug ("Reading file " ^ f)
    ; case readFile f of
          SOME input => Ast.parse_prg {srcname=f,input=input}
        | NONE => raise Fail ("Cannot read file " ^ f)
    )

fun parseEval () =
    let val () = if List.null srcs andalso exp_str() = "" then
                   raise Fail "Expects one or more source files or an expression argument"
                 else ()

        val prg = List.concat (map parse srcs)

        val exp_opt =
            case exp_str() of
                "" => NONE
              | exp_s => SOME (exp_s, Ast.parse {srcname="arg",input=exp_s})

        (* type inference *)
        val () = debug "Type inference"
        val (prg',TE) = Ast.tyinf_prg prg

        val exp_opt' =
            case exp_opt of
                NONE => NONE
              | SOME (s,e) =>
                let val (e',ty) = Ast.tyinf_exp (Ast.plus(Ast.TEinit,TE)) e
                in SOME(s,e',ty)
                end

        val () =
            if print_typed_p() then
              ( println "Typed program:"
              ; List.app (fn (f,x,e,(r,ty)) =>
                             ( println (" " ^ f ^ " : " ^ Ast.pr_ty ty)
                             ; println (" " ^ f ^ "(" ^ x ^ ") = " ^ Ast.pr_exp e)
                             )) prg'
              ; case exp_opt' of
                    NONE => ()
                  | SOME(s,e',ty) =>
                    println (" expr : " ^ Ast.pr_ty ty ^ " = " ^ Ast.pr_exp e')
              )
            else ()

        val () =
            case exp_opt' of
                NONE => debug ("Nothing to evaluate - exiting")
              | SOME (exp_s, exp, ty) =>
                let val () = debug ("Evaluating '" ^ exp_s ^ "'")
                    val v = Ast.eval_exp (fn (r,_) => r) prg' exp
                in println (" " ^ exp_s ^ " = " ^ Ast.pr_v v)
                end
    in (prg', exp_opt')
    end

(* Instantiate AD framework *)
structure Ad = AD(TermVal)
open Ad
structure V = TermVal

(* Compile AST representation into AD framework expression representation *)

fun compile (prg, exp_opt) =
    let
      fun ce e =
          case e of
              Ast.Real(f,_) => E.DSL.const (V.R f)
            | Ast.Int(i,(r,t)) =>
              if Ast.is_real t then E.DSL.const (V.R (Real.fromInt i))
              else dieReg r "compile: integer not resolved to real"
            | Ast.Zero _ => E.DSL.const V.Z
            | Ast.Let(v,e1,e2,_) => E.DSL.lett(v,ce e1, ce e2)
            | Ast.Add(e1,e2,_) => E.DSL.+(ce e1, ce e2)
            | Ast.Sub(e1,e2,_) => E.DSL.-(ce e1, ce e2)
            | Ast.Mul(e1,e2,_) => E.DSL.*(ce e1, ce e2)
            | Ast.Smul(e1,e2,_) => E.DSL.*(ce e1, ce e2)
            | Ast.Var(v,_) => E.DSL.V v
            | Ast.App("ln",e,_) => E.DSL.ln(ce e)
            | Ast.App("sin",e,_) => E.DSL.sin(ce e)
            | Ast.App("cos",e,_) => E.DSL.cos(ce e)
            | Ast.App("exp",e,_) => E.DSL.exp(ce e)
            | Ast.App("cprod3",e,_) => E.DSL.cprod3(ce e)
            | Ast.App("cross",e,_) => E.DSL.cprod3(ce e)
            | Ast.App("dprod",e,_) => E.DSL.dprod(ce e)
            | Ast.App("dprod3",e,_) => E.DSL.dprod(ce e)
            | Ast.App("sprod",e,_) => E.DSL.sprod(ce e)
            | Ast.App("norm2sq",e,_) => E.DSL.norm2sq(ce e)
            | Ast.Tuple(es,_) => E.DSL.tup (List.map ce es)
            | Ast.Prj(i,e,(r,_)) =>
              let val t = #2(Ast.info_of_exp e)
              in case Ast.un_tuple t of
                     SOME tys => E.DSL.prj(length tys,i,ce e)
                   | NONE => dieReg r ("compile: unresolved tuple - type is " ^ Ast.pr_ty t)
              end
            | Ast.App(f,e,_) => E.DSL.apply(f,ce e)
            | Ast.Pow(f,e,_) => E.DSL.pow f (ce e)
            | Ast.Map(x,f,es,_) => E.DSL.map (x, ce f, ce es)
            | Ast.Iota(n,_)  => E.DSL.const (V.iota n)
            | Ast.Red(rel,es,(r,_)) =>
                 let fun compile_index e : Rel.index =
                      case e of
                         Ast.Int(n,_)    => Rel.Single n
                       | Ast.Array(es,_) =>
                           Rel.Enum (map (fn (Ast.Int(n,_)) => n | e => dieReg r (Ast.pr_exp e)) es)
                       | Ast.Range(Ast.Int(from,_),Ast.Int(to,_),Ast.Int(step,_),_)  =>
                         Rel.Range(from,to,step)
                       | _ => dieReg r ("compile_index: unsupported index: " ^ Ast.pr_exp e)
                    fun compile_rel rel =
                      case rel of
                         Ast.Func("to",SOME (Ast.Int(n,_)),from,to,_) =>
                           Rel.Func(Rel.To n, compile_index from, compile_index to)
                        | Ast.Trans (r,_) => Rel.Trans (compile_rel r)
                        | Ast.Comp(r1,r2,_)  => Rel.Comp(compile_rel r1, compile_rel r2)
                        | Ast.Pairs(Ast.Array(es,_),_)  =>
                           Rel.Pairs (map (fn (Ast.Tuple ([Ast.Int(x,_),Ast.Int(y,_)],_)) => (x,y) | _ => dieReg r "oops2") es)
                        | _ => dieReg r ("compile_rel: unsupported rel: " ^ Ast.pr_rel rel)
                 in E.DSL.red(compile_rel rel, ce es)
                 end
            | e  => dieReg (#1(Ast.info_of_exp e)) ("compile: unsupported exp: " ^ Ast.pr_exp e)
      fun cf (f,x,e:(Region.reg*Ast.ty) Ast.exp,i) : string*string*E.e*(Region.reg*Ast.ty) =
          (f,x,ce e,i)
      val () = debug("Compiling program")
      val prg' = List.map cf prg
      val () = if print_exp_p() then
                 ( println("Internal expression program:")
                 ; List.app (fn (f,x,e,_) => println (" " ^ f ^ "(" ^ x ^ ") = " ^ E.pp e)) prg'
                 )
               else ()

    in prg'
    end

(* Translate expression programs into point-free notation *)
fun translate prg =
    let fun transl (f,x,e,i) =
            (f, F.opt(E.trans [x] e),i)
        val () = debug ("Translating program")
        val prg' = map transl prg
        val () = if print_pointfree_p() then
                   ( println("Point free notation:")
                   ; List.app (fn (f,e,i) => println (" " ^ f ^ " = " ^ F.pp e)) prg'
                   )
                 else ()
    in prg'
    end

(* Differentiation *)

fun differentiate prg =
    let fun diff E nil = nil
          | diff E ((f,e,(r,t))::rest) =
            let val arg =
                    case Ast.un_fun t of
                        SOME(ty,ty') =>
                        (case Ast.un_tuple ty of
                             SOME tys =>
                             V.T(mapi (fn (ty,i) => V.Var ("x" ^ Int.toString(i+1))) tys)
                           | NONE =>
                             (if Ast.is_real ty then V.Var "x"
                              else case Ast.un_array ty of
                                       SOME _ => V.Var "xs"
                                     | NONE => dieReg r "expecting tuple type, array type, pr type real as argument type"))
                      | NONE => dieReg r "expecing function type"
                val M = D.diffM E e arg
                val E' = (f,e)::E
            in (f,arg,M,(r,t)) :: diff E' rest
            end
        val () = debug "Differentiating program"
        val prg' = diff nil prg
        fun ppM pp M = V.ppM "    " pp M
        infix >>= val op >>= = V.>>=
        val ret = V.ret
        val () =
            if print_diff_p() then
              ( println "Differentiated program (linear map expression):"
              ; List.app (fn (f,arg,M,_) =>
                             let val fM = M >>= (fn (_,l) => ret l)
                                 val rM = fM >>= (ret o L.adjoint)
                             in println (" " ^ f ^ " " ^ V.pp arg ^ " =")
                              ; println (ppM (fn (r,_) => V.pp r) M)
                              ; println (" " ^ f ^ "' " ^ V.pp arg ^ " =")
                              ; println (ppM L.pp fM)
                              ; println (" " ^ f ^ "^ " ^ V.pp arg ^ " =")
                              ; println (ppM L.pp rM)
                              ; println ""
                             end) prg'
              )
            else ()
    in prg'
    end

fun unlinearise prg =
    let fun unlin (f,arg,M,(r,t)) =
            let val d =
                    case Ast.un_fun t of
                        SOME(ty,ty') =>
                        if rad_p() then
                          (case Ast.un_tuple ty' of
                               SOME tys =>
                               V.T (mapi (fn (ty,i) =>
                                             V.Var("dy" ^ Int.toString (i+1))) tys)
                             | NONE =>
                               if Ast.is_real ty' then V.Var "dy"
                               else case Ast.un_array ty' of
                                        SOME _ => V.Var "dys"
                                      | NONE => dieReg r "expecting tuple type, array type, or real type as result type")
                        else (case Ast.un_tuple ty of
                                  SOME tys =>
                                  V.T (mapi (fn (ty,i) =>
                                                V.Var("dx" ^ Int.toString (i+1))) tys)
                                | NONE =>
                                  if Ast.is_real ty then V.Var "dx"
                                  else case Ast.un_array ty of
                                           SOME _ => V.Var "dxs"
                                         | NONE => dieReg r "expecting tuple type, array type, or real type as argument type")
                      | NONE => dieReg r "expecing function type"
                infix >>= val op >>= = V.>>=
                val ret = V.ret
                val fM = M >>= (fn (_,l) => ret l)
                val dM = if rad_p() then
                           fM >>= (ret o L.adjoint)
                         else fM
                val gM = dM >>= (fn l => L.eval l d)
                val gM = V.simpl gM
            in (f,arg,d,gM,(r,t))
            end
        val prg' = List.map unlin prg
        val pling = if rad_p() then "^" else "'"
        val () =
            if print_diff_unlinearised_p() then
              ( println "Unlinearised differentiated program:"
              ; List.app (fn (f,arg,d,gM,_) =>
                             ( println (" " ^ f ^ pling ^ " " ^ V.pp arg ^ " " ^ V.pp d ^ " =")
                             ; println (V.ppM "    " V.pp gM)
                             ; println "")
                         ) prg'
              )
            else ()
    in prg'
    end


fun main () =
    let val parseRes = parseEval()
        val compRes = compile parseRes
        val transRes = translate compRes
        val diffRes = differentiate transRes
        val udiffRes = unlinearise diffRes
    in ()
    end handle Fail msg =>
               ( println ("** ERROR: " ^ msg)
               ; println ("** ERROR: Pass the --help option for assistance")
               ; OS.Process.exit OS.Process.failure
               )

val () = main ()
