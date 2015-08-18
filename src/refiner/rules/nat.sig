signature NAT_RULES =
sig
  type tactic
  type name
  type hyp
  type term

  (* H >> nat = nat ∈ U{k} *)
  val NatEq : tactic

  (* H, z : nat, H' >> C[z]
   *   H, z : nat, H' >> C[0]
   *   H, z : nat, i : nat, p : C[i], H' >> C[s(i)]
   *)
  val NatElim : hyp * (name * name) option -> tactic
  val ZeroEq : tactic
  val SuccEq : tactic
  val NatRecEq : term option * (name * name) option -> tactic
end
