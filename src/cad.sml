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

structure Ad = AD(TermVal)
open Ad
structure V = TermVal

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
    in List.map cf prg
    end


fun main () =
    let val parseResult = parseEval()
        val _ = compile parseResult
    in ()
    end handle Fail msg =>
               ( println ("** ERROR: " ^ msg)
               ; println ("** ERROR: Pass the --help option for assistance")
               ; OS.Process.exit ~1
               )

val () = main ()
