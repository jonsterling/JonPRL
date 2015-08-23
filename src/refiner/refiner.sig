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
    where type resource = Resource.t

  type world = Development.world
  type hyp = name HypSyn.t

  structure Rules :
  sig
    structure UnivRules : UNIV_RULES
      where type tactic = tactic

    structure EqRules : EQ_RULES
      where type tactic = tactic
      where type term = term
      where type hyp = hyp

    structure FunRules : FUN_RULES
      where type tactic = tactic
      where type term = term
      where type hyp = hyp
      where type name = name

    structure ISectRules : ISECT_RULES
      where type tactic = tactic
      where type term = term
      where type hyp = hyp
      where type name = name

    structure SubsetRules : SUBSET_RULES
      where type tactic = tactic
      where type term = term
      where type hyp = hyp
      where type name = name

    structure NatRules : NAT_RULES
      where type tactic = tactic
      where type term = term
      where type hyp = hyp
      where type name = name

    structure BaseRules : BASE_RULES
      where type tactic = tactic
      where type hyp = hyp
      where type name = name

    structure ImageRules : IMAGE_RULES
      where type tactic = tactic
      where type name = name
      where type hyp = hyp

    structure GeneralRules : GENERAL_RULES
      where type tactic = tactic
      where type term = term
      where type hyp = hyp
      where type name = name
      where type operator = operator
      where type conv = conv
      where type world = world

    structure ProdRules : PROD_RULES
      where type tactic = tactic
      where type term = term
      where type hyp = hyp
      where type name = name

    structure PlusRules : PLUS_RULES
      where type tactic = tactic
      where type term = term
      where type hyp = hyp
      where type name = name

    structure AtomRules : ATOM_RULES
      where type tactic = tactic
      where type name = name

    structure CEqRules : CEQ_RULES
      where type tactic = tactic
      where type term = term
      where type hyp = hyp

    structure ApproxRules : APPROX_RULES
      where type tactic = tactic
      where type term = term
      where type hyp = hyp
      where type name = name

    structure BHypRules : BHYP_RULES
      where type tactic = tactic
      where type hyp = hyp

    structure WTreeRules : WTREE_RULES
      where type tactic = tactic
      where type term = term
      where type hyp = hyp
      where type name = name
  end

  structure Conversions :
  sig
    val Step : conv
  end
end
