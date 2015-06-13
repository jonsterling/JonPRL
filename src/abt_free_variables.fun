functor AbtFreeVariables (Abt : ABT) : ABT_FREE_VARIABLES =
struct
  structure Abt = Abt

  open Abt
  infix $ \

  structure Set = SplaySet (structure Elem = Abt.Variable)

  local
    fun go B (p $ es) R =
        Vector.foldl (fn (x,y) => Set.union x y) R (Vector.map (fn E => go B (out E) R) es)
      | go B (`x) R = if Set.member B x then R else Set.insert R x
      | go B (x \ E) R = go (Set.insert B x) (out E) R
  in
    fun free_variables M =
      go Set.empty (out M) Set.empty
  end
end
