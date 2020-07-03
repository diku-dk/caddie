datatype t = A of real | B
fun pp p = case p of
               A r => Real.toString r
             | B => "uggh"
val () = print "hi"
val p = A 1.0
val () = print (pp p)
val () = print "\n"
