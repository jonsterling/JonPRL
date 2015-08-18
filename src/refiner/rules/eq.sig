signature EQ_RULES =
sig
  type tactic
  type term
  type hyp

  (* H >> (M = N ∈ A) = (M' = N' ∈ A') ∈ U{k}
   * 1. H >> A = A' ∈ U{k}
   * 2. H >> M = M' ∈ A
   * 3. H >> N = N' ∈ A *)
  val EqEq : tactic

  (* H >> (M = N ∈ A) = (M' = N' ∈ A') ∈ U{k}
   * 1. H >> A = A' ∈ U{k}
   * 2. H >> M = M' ∈ (A |_| Base)
   * 3. H >> N = N' ∈ (A |_| Base) *)
  val EqEqBase : tactic
  val EqMemEq : tactic
  val EqSym : tactic
  val EqSubst : term * term * Level.t option -> tactic
  val HypEqSubst : Dir.dir * hyp * term * Level.t option -> tactic
end
