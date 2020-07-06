functor AD (V : VAL) = struct
  structure V = V
  structure D = Diff(V)
  structure F = D.F
  structure E = Exp(structure V = V
                    structure F = F)
  structure L = D.L
end
