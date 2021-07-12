signature REL = sig
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

val single   : int -> index
val enum     : int list -> index
val range    : int * int * int -> index
val id       : func
val to       : int -> func
val t        : func -> func
val func     : func * index * index -> r
val comp     : r * r -> r
val pairs     : (int * int) list -> r
val pp       : r -> string
val trans    : r -> r
val eval     : r -> (int * int) list
val toFunc   : r -> int -> int list
val domain   : r -> index
val codomain : r -> index
val eval_index : index -> int list
end
