signature ATOM_RULES =
sig
  type tactic
  type name

  val Eq : tactic
  val TokenEq : tactic
  val TestEq : name option -> tactic
  val TestReduceLeft : tactic
  val TestReduceRight : tactic

  (* H >> match u with {P*} = match u' with {Q*} ∈ C by MatchTokenEq
   *   H >> u = u' ∈ atom
   *   H >> P*@t = Q*@t ∈ C for all t ∈ dom[P*]
   *           requires: dom[P*] ~ [Q*]
   *   H, x : match u with {P*} ~ P*@_, y : match u' with {Q*} ~ Q*@_ >> P*@_ = Q*@_ ∈ C
   *)
  val MatchTokenEq : tactic
end
