signature UNIV_RULES =
sig
  type tactic

  (* H >> A = B ∈ U{l} by Cum k (k < l)
   * 1.  H >> A = B ∈ U{k}
   *)
  val Cum : Level.t option -> tactic

  (* H >> U{l} = U{l} ∈ U{k} by UnivEq (l < k) *)
  val Eq : tactic
end
