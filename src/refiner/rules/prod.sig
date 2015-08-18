signature PROD_RULES =
sig
  type name
  type tactic
  type term
  type hyp

  (* H >> (Σx:A)B[x] = (Σx:A')B'[x] ∈ U{k} by ProdEq z
   * 1. H >> A = A' ∈ U{k}
   * 2. H, z : A >> B[z] = B'[z] ∈ U{k}
   *)
  val ProdEq : name option -> tactic

  (* H >> (Σx:A)B[x] by ProdIntro M
   * 1. H >> M ∈ A
   * 2. H >> B[M]
   * 3. H, x:A >> B[x] ∈ U{k}
   *)
  val ProdIntro : term * name option * Level.t option -> tactic
  val IndependentProdIntro : tactic

  (* H, z : (Σx:A)B[x], H'[z] >> P[z] by ProdElim z (s, t)
   * H, z : (Σx:A)B[x], s : A, t : B[s], H'[<s,t>] >> P[<s,t>]
   *)
  val ProdElim : hyp * (name * name) option -> tactic
  val PairEq : name option * Level.t option -> tactic
  val SpreadEq : term option * term option * (name * name * name) option -> tactic
end
