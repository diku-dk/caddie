structure Rel : REL = struct

datatype index = Single of int
               | Enum of int list
               | Range of int * int * int

datatype func = Id
              | To of int
              | T of func

datatype r = Func of func * index * index
             | Trans of r
             | Comp of r * r
             | Pairs of (int * int) list

val single = Single
val enum = Enum
val range = Range
val id = Id
val to = To
val t = T
val func = Func
val comp = Comp
val pairs = Pairs

fun pp_index d =
    case d of
      Single x => Int.toString x
    | Enum xs => "[" ^ String.concatWith "," (map Int.toString xs) ^ "]"
    | Range (from, to, step)  => "range(" ^ Int.toString from ^ "," ^ Int.toString  to ^ "," ^ Int.toString step ^ ")"

fun pp_func f =
    case f of
      Id => "Id"
    | To x => "(To " ^ Int.toString x  ^ ")"
    | T f => "(" ^ pp_func f ^ ")!"

fun pp r =
    case r of
       Func (f, x, y) => "(" ^ pp_func f ^ "," ^ pp_index x ^ "," ^ pp_index y ^ ")"
     | Trans r => "(" ^ pp r ^ ")!"
     | Comp (r2, r1) => "(" ^ pp r2 ^ " o " ^ pp r1 ^ ")"
     | Pairs xys => "[" ^ String.concatWith "," (List.map (fn (x,y) => "(" ^ Int.toString x ^ "," ^ Int.toString y ^ ")" ) xys) ^ "]"

fun trans (r : r) : r =
  case r of
     Func (T f,from,to) => Func (f, to, from)
   | Func (f,from,to) => Func (T f, to, from)
   | Trans r => r
   | Comp (r2, r1) => Comp (trans r1, trans r2)

fun eval_idx i : int list =
  case i of
     Single x => [x]
   | Enum xs  => xs
   | Range (from, to, step) =>
       let fun eval_range (from, to, step) =
             if from < to
             then from :: eval_range (from + step, to, step)
             else nil
       in eval_range (from, to, step)
       end

fun eval_f f from to : (int * int) list =
    case f of
        Id => map (fn i => (i, i)) (eval_idx from)
      | To x => map (fn i => (i, x)) (eval_idx from)
      | T f => eval_f f to from

fun eval (r : r) : (int * int) list =
    case r of
      Func (f,from,to) => eval_f f from to

fun toFunc (r: r) (x : int) : int list =
    map (#2) (#1 (List.partition (fn (y,_) => y = x) (eval r)))

fun domain (r:r) : index =
    case r of
       Func(_,from,_) => from
     | Trans r => codomain r
     | Comp(_,r2) => domain r2
     | Pairs xys => Enum (map #1 xys) (* todo: remove duplicates *)
and codomain (r:r) : index =
    case r of
       Func(_,_,to) => to
     | Trans r => domain r
     | Comp(r1,_) => codomain r1
     | Pairs xys => Enum (map #2 xys) (* todo: remove duplicates *)

fun eval_index (i : index) : int list =
    case i of
       Single x => [x]
     | Enum xs =>  xs
     | Range(from,to,step) =>
         let fun eval_range (from, to, step) =
               if from < to
               then from :: eval_range (from + step, to, step)
               else nil
         in eval_range (from, to, step)
         end
end
