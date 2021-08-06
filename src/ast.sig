signature AST = sig

  datatype 'i exp = Real of real * 'i
                  | Int of int * 'i
                  | Zero of 'i
                  | Let of string * 'i exp * 'i exp * 'i
                  | Add of 'i exp * 'i exp * 'i
                  | Sub of 'i exp * 'i exp * 'i
                  | Mul of 'i exp * 'i exp * 'i
                  | Smul of 'i exp * 'i exp * 'i
                  | Var of string * 'i
                  | App of string * 'i exp * 'i
                  | Tuple of 'i exp list * 'i
                  | Prj of int * 'i exp * 'i
                  | Map of string * 'i exp * 'i exp * 'i
                  | Iota of int * 'i
                  | Pow of real * 'i exp * 'i
                  | Red of 'i rel * 'i exp * 'i
                  | Array of 'i exp list * 'i
                  | Range of 'i exp * 'i exp * 'i exp * 'i
       and 'i rel = Func of string * ('i exp) option * 'i exp * 'i exp * 'i
                  | Trans of 'i rel * 'i
                  | Comp of 'i rel * 'i rel * 'i
                  | Pairs of 'i exp * 'i

  val pr_exp      : 'i exp -> string
  val pr_rel      : 'i rel -> string
  val info_of_exp : 'i exp -> 'i

  type v
  val pr_v : v -> string
  val real_v : real -> v

  type 'a env
  val look    : 'a env -> string -> 'a option
  val insert  : 'a env -> string * 'a -> 'a env
  val plus    : 'a env * 'a env -> 'a env

  val VEinit  : v env
  val VEempty : v env
  val eval    : ('i -> Region.reg) -> v env -> 'i exp -> v

  val parse   : {srcname:string,input:string} -> Region.reg exp

  type 'i prg = (string * string * 'i exp * 'i) list

  val pr_prg    : 'i prg -> string
  val eval_prg  : ('i -> Region.reg) -> 'i prg -> string -> v -> v
  val eval_exp  : ('i -> Region.reg) -> 'i prg -> 'i exp -> v
  val parse_prg : {srcname:string,input:string} -> Region.reg prg

  type ty
  val real_ty   : ty
  val tuple_ty  : ty list -> ty
  val fun_ty    : ty * ty -> ty
  val rel_ty    : ty * ty -> ty
  val fresh_ty  : unit -> ty
  val eq_ty     : ty * ty -> bool
  val unify_ty  : Region.reg -> ty * ty -> unit           (* may raise Fail *)
  val pr_ty     : ty -> string

  val un_tuple  : ty -> ty list option
  val un_array  : ty -> ty option
  val un_fun    : ty -> (ty*ty)option
  val is_real   : ty -> bool

  val TEinit    : ty env
  val TEempty   : ty env
  val tyinf_exp : ty env -> Region.reg exp -> (Region.reg*ty) exp * ty
  val tyinf_prg : Region.reg prg -> (Region.reg*ty) prg * ty env
end
