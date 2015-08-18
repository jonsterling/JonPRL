signature REFINER =
sig
  type name
  type term

  type conv
  type tactic
  type operator

  exception Refine

  structure Sequent : SEQUENT
    where type term = term

  structure Development : DEVELOPMENT
    where type tactic = tactic
    where type judgement = Sequent.sequent
    where type operator = operator

  type world = Development.world
  type hyp = name HypSyn.t

  structure Rules : sig
    include UNIV_RULES where type tactic = tactic

    val Fiat : tactic
    val EqEq : tactic
    val EqEqBase : tactic
    val EqMemEq : tactic

    val ProdEq : name option -> tactic
    val ProdIntro : term * name option * Level.t option -> tactic
    val IndependentProdIntro : tactic
    val ProdElim : hyp * (name * name) option -> tactic

    val PairEq : name option * Level.t option -> tactic
    val SpreadEq : term option * term option * (name * name * name) option -> tactic
    val PlusEq : tactic
    val PlusIntroL : Level.t option -> tactic
    val PlusIntroR : Level.t option -> tactic
    val PlusElim : (hyp * (name * name) option) -> tactic
    val InlEq : Level.t option -> tactic
    val InrEq : Level.t option -> tactic
    val DecideEq : term
                   -> (term * term * (name * name * name) option)
                   -> tactic

    val FunEq : name option -> tactic
    val FunIntro : name option * Level.t option -> tactic
    val FunElim : hyp * term * (name * name) option -> tactic
    val LamEq : name option * Level.t option -> tactic
    val ApEq : term option -> tactic
    val FunExt : name option * Level.t option -> tactic

    val IsectEq : name option -> tactic
    val IsectIntro : name option * Level.t option -> tactic
    val IsectElim : hyp * term * (name * name) option -> tactic
    val IsectMemberEq : name option * Level.t option -> tactic
    val IsectMemberCaseEq : term option * term -> tactic

    val SubsetEq : name option -> tactic
    val SubsetIntro : term * name option * Level.t option -> tactic
    val IndependentSubsetIntro : tactic
    val SubsetElim : hyp * (name * name) option -> tactic
    val SubsetMemberEq : name option * Level.t option -> tactic
    val NatEq : tactic
    val NatElim : hyp * (name * name) option -> tactic

    val ZeroEq : tactic
    val SuccEq : tactic
    val NatRecEq : term option * (name * name) option -> tactic

    val BaseEq : tactic
    val BaseIntro : tactic
    val BaseMemberEq : tactic
    val BaseElimEq : hyp * name option -> tactic

    val Witness : term -> tactic

    val Assumption : tactic
    val Assert : term * name option -> tactic
    val Hypothesis : hyp -> tactic
    val HypEq : tactic
    val EqInSupertype : tactic

    val Unfolds : world * (operator * Level.t option) list -> tactic
    val Lemma : world * operator -> tactic
    val BHyp : hyp -> tactic

    val RewriteGoal : conv -> tactic

    val EqSubst : term * term * Level.t option -> tactic
    val HypEqSubst : Dir.dir * hyp * term * Level.t option -> tactic
    val EqSym : tactic

    val CEqEq       : tactic
    val CEqMemEq    : tactic
    val CEqSym      : tactic
    val CEqStep     : tactic
    val CEqSubst    : term * term -> tactic
    val HypCEqSubst : Dir.dir * hyp * term -> tactic
    val CEqStruct   : tactic
    val CEqApprox   : tactic

    val ApproxEq    : tactic
    val ApproxMemEq : tactic
    val ApproxExtEq : tactic
    val ApproxElim : hyp -> tactic
    val ApproxRefl  : tactic

    val BottomDiverges : hyp -> tactic
    val AssumeHasValue : (name option * Level.t option) -> tactic
    val ImageEq    : tactic
    val ImageMemEq : tactic
    val ImageElim  : hyp * name option -> tactic
    val ImageEqInd : hyp * (name * name * name * name) option -> tactic

    val AtomEq : tactic
    val TokenEq : tactic
    val TestAtomEq : name option -> tactic
    val TestAtomReduceLeft : tactic
    val TestAtomReduceRight : tactic

    val MatchTokenEq : tactic
    val MatchSingle : (name * term) list * term * ((name * term) list -> tactic)
                      -> tactic

    val Thin : hyp -> tactic
  end

  structure Conversions :
  sig
    val Step : conv
  end
end
