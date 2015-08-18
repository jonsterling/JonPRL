signature APPROX_RULES =
sig
  type tactic
  type hyp
  type name
  type term

  val Eq    : tactic
  val MemEq : tactic
  val ExtEq : tactic
  val Elim : hyp -> tactic
  val Refl  : tactic

  (* H, x : has-value(bot), J >> P
   *)
  val BottomDiverges : hyp -> tactic

  (* H >> approx(M;N)
   *   H, y : has-value(M) >> approx(M;N)
   *   H >> has-value(M) in U{k}
   *)
  val AssumeHasValue : (name option * Level.t option) -> tactic
end
