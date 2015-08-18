signature EQ_RULES =
sig
  type tactic
  type term
  type hyp

  (* H >> (M = N ∈ A) = (M' = N' ∈ A') ∈ U{k}
   * 1. H >> A = A' ∈ U{k}
   * 2. H >> M = M' ∈ A
   * 3. H >> N = N' ∈ A *)
  val Eq : tactic

  (* H >> (M = N ∈ A) = (M' = N' ∈ A') ∈ U{k}
   * 1. H >> A = A' ∈ U{k}
   * 2. H >> M = M' ∈ (A |_| Base)
   * 3. H >> N = N' ∈ (A |_| Base) *)
  val EqBase : tactic
  val MemEq : tactic
  val Sym : tactic
  val Subst : term * term * Level.t option -> tactic
  val HypSubst : Dir.dir * hyp * term * Level.t option -> tactic
end
