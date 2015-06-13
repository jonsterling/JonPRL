signature ABT_FREE_VARIABLES =
sig
  structure Abt : ABT
  structure Set : SET
  sharing type Set.elem = Abt.Variable.t

  val free_variables : Abt.t -> Set.set
end
