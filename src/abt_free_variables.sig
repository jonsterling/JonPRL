signature ABT_freeVariables =
sig
  structure Abt : ABT
  structure Set : SET
  sharing type Set.elem = Abt.Variable.t

  val freeVariables : Abt.t -> Set.set
end
