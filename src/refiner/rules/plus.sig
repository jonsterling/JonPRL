signature PLUS_RULES =
sig
    type tactic
    type name
    type hyp
    type term

    (* H >> A + B = A' + B' ∈ U{k}
     *   H >> A' = A' ∈ U{k}
     *   H >> B' = B' ∈ U{k}
     *)
    val PlusEq : tactic

    (* H >> inl X ∈ A + B
     *  H >> X ∈ A
     *  H >> B ∈ U{k}
     *)
    val PlusIntroL : Level.t option -> tactic

    (* H >> inl X ∈ A + B
     *  H >> X ∈ B
     *  H >> A ∈ U{k}
     *)
    val PlusIntroR : Level.t option -> tactic

    (* H, x : A + B >> C
     *   H, x : A + B, y : A >> C
     *   H, x : A + B, z : B >> C
     *)
    val PlusElim : (hyp * (name * name) option) -> tactic

    (* H >> inl X = inl Y ∈ A + B
     *    H >> X = Y ∈ A
     *    H >> B ∈ U{k}
     *)
    val InlEq : Level.t option -> tactic

    (* H >> inr X = inr Y ∈ A + B
     *    H >> X = Y ∈ B
     *    H >> A ∈ U{k}
     *)
    val InrEq : Level.t option -> tactic
    val DecideEq : term
                   -> (term * term * (name * name * name) option)
                   -> tactic
end
