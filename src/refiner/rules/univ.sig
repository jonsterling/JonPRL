signature UNIV_RULES =
sig
  structure Lcf : LCF

  val Cum : Level.t option -> Lcf.tactic
  val UnivEq : Lcf.tactic
end
