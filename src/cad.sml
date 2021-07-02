(* Some utility functions *)

fun println s = print (s ^ "\n")

fun readFile f =
    let val is = TextIO.openIn f
    in let val c = TextIO.inputAll is
       in TextIO.closeIn is
        ; SOME c
       end handle _ => (TextIO.closeIn is; NONE)
    end

(* Option specifications *)

val rev_ad_p = CmdArgs.addFlag ("r", SOME ["Apply reverse mode AD."])

val verbose_p = CmdArgs.addFlag ("-verbose", SOME ["Be verbose."])

val exp_str = CmdArgs.addString ("e", "", SOME ["Expression to be evaluated after loading of program files."])

val () = CmdArgs.addUsage ("-help", "options... file1.cad ... fileN.cad")

val () = CmdArgs.addVersion ("-version", "Combinatory AD (CAD) v0.0.1")

val print_exp_p = CmdArgs.addFlag ("-Pexp", SOME ["Print internal expression program."])
val print_pointfree_p = CmdArgs.addFlag ("-Ppointfree", SOME ["Print point free internal expression program."])

val srcs = CmdArgs.processOptions()

fun debug s =
    if verbose_p() then println ("[" ^ s ^ "]")
    else ()

(* Parsing and possibly evaluation *)

fun parse f =
    ( debug ("Reading file " ^ f)
    ; case readFile f of
          SOME input => Ast.parse_prg {srcname=f,input=input}
        | NONE => raise Fail ("Error reading file " ^ f)
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

        val () =
            case exp_opt of
                NONE => debug ("Nothing to evaluate - exiting")
              | SOME (exp_s, exp) =>
                let val () = debug ("Evaluating '" ^ exp_s ^ "'")
                    val v = Ast.eval_exp prg exp
                in println (exp_s ^ " = " ^ Ast.pp_v v)
                end
    in (prg, exp_opt)
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
              Ast.Real r => E.DSL.const (V.R r)
            | Ast.Let(v,e1,e2) => E.DSL.lett(v,ce e1, ce e2)
            | Ast.Add(e1,e2) => E.DSL.+(ce e1, ce e2)
            | Ast.Sub(e1,e2) => E.DSL.-(ce e1, ce e2)
            | Ast.Mul(e1,e2) => E.DSL.*(ce e1, ce e2)
            | Ast.Var v => E.DSL.V v
            | Ast.App("ln",e) => E.DSL.ln(ce e)
            | Ast.App("sin",e) => E.DSL.sin(ce e)
            | Ast.App("cos",e) => E.DSL.cos(ce e)
            | Ast.App("exp",e) => E.DSL.exp(ce e)
            | _ => raise Fail "not implemented"
      fun cf (f,x,e:Ast.exp) : string*string*E.e =
          (f,x,ce e)
      val () = debug("Compiling program")
      val prg' = List.map cf prg
      val () = if print_exp_p() then
                 ( println("Internal expression program:")
                 ; List.app (fn (f,x,e) => println (" " ^ f ^ "(" ^ x ^ ") = " ^ E.pp e)) prg'
                 )
               else ()

    in prg'
    end

(* Translate expression programs into point-free notation *)
fun translate prg =
    let fun transl (f,x,e) = (f, E.trans [x] e)
        val () = debug ("Translating program")
        val prg' = map transl prg
        val () = if print_pointfree_p() then
                   ( println("Point free notation:")
                   ; List.app (fn (f,e) => println (" " ^ f ^ " = " ^ F.pp e)) prg'
                   )
                 else ()
    in prg'
    end

fun main () =
    let val parseRes = parseEval()
        val compRes = compile parseRes
        val transRes = translate compRes
    in ()
    end handle Fail msg =>
               ( println ("** ERROR: " ^ msg)
               ; println ("** ERROR: Pass the --help option for assistance")
               ; OS.Process.exit OS.Process.failure
               )

val () = main ()
