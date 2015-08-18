signature BHYP_RULES =
sig
  type tactic
  type hyp

  val BHyp : hyp -> tactic
end
