signature PLUS_RULES =
sig
    type tactic
    type name
    type hyp
    type term

    val PlusEq : tactic
    val PlusIntroL : Level.t option -> tactic
    val PlusIntroR : Level.t option -> tactic
    val PlusElim : (hyp * (name * name) option) -> tactic
    val InlEq : Level.t option -> tactic
    val InrEq : Level.t option -> tactic
    val DecideEq : term
                   -> (term * term * (name * name * name) option)
                   -> tactic
end
