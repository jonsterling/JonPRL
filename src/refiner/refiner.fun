functor Refiner
  (structure Syntax : ABT_UTIL
     where type Operator.t = UniversalOperator.t
   structure Sequent : SEQUENT
     where type term = Syntax.t
     where Context.Syntax = Syntax
   structure Lcf : LCF
     where type evidence = Syntax.t
     where type goal = Sequent.sequent Goal.goal

   structure Development : DEVELOPMENT
     where type judgement = Sequent.sequent
     where type evidence = Lcf.evidence
     where type tactic = Lcf.tactic
     where type operator = UniversalOperator.t
     where type resource = Resource.t

   structure Conv : CONV where type term = Syntax.t
   structure Semantics : SMALL_STEP where type syn = Syntax.t
   sharing type Development.term = Syntax.t
   structure Builtins : BUILTINS
     where type Conv.term = Conv.term) : REFINER =
struct
  structure Lcf = Lcf
  structure Conv = ConvUtil(structure Conv = Conv and Syntax = Syntax)
  structure Syntax = Syntax

  structure Sequent = Sequent
  structure Development = Development

  type tactic = Lcf.tactic
  type conv = Conv.conv
  type name = Sequent.name
  type term = Syntax.t
  type goal = Sequent.sequent

  type operator = Syntax.Operator.t
  type hyp = name HypSyn.t

  type world = Development.world

  exception Refine

  structure Rules =
  struct
    structure Utils = RulesUtil
      (structure Lcf = Lcf
       structure Syntax = Syntax
       structure Conv = Conv
       structure Semantics = Semantics
       structure Sequent = Sequent
       structure Development = Development
       structure Builtins = Builtins
       exception Refine = Refine)

    structure UnivRules = UnivRules(Utils)
    structure EqRules = EqRules(Utils)
    structure FunRules = FunRules(Utils)
    structure ISectRules = ISectRules(Utils)
    structure SubsetRules = SubsetRules(Utils)
    structure NatRules = NatRules(Utils)
    structure BaseRules = BaseRules(Utils)
    structure ImageRules = ImageRules(Utils)
    structure PerRules = PerRules(Utils)
    structure GeneralRules = GeneralRules(Utils)
    structure ProdRules = ProdRules(Utils)
    structure PlusRules = PlusRules(Utils)
    structure AtomRules = AtomRules(Utils)
    structure CEqRules = CEqRules(Utils)
    structure ApproxRules = ApproxRules(Utils)
    structure WTreeRules = WTreeRules(Utils)

    (* BHyp gets its own special functor because it depends
     * on a number of other tactics.
     *)
    structure BHypRules = BHypRules
     (structure U = Utils
      val FunElim = FunRules.Elim
      val IsectElim = ISectRules.Elim
      val Thin = GeneralRules.Thin)
  end

  structure Conversions =
  struct
    open Conv

    val Step : conv = fn M =>
      case Semantics.step M of
           Semantics.STEP M' => M'
         | _ => raise Conv
  end
end

structure Refiner = Refiner
  (structure Lcf = Lcf
   structure Syntax = Syntax
   structure Conv = Conv
   structure Semantics = Semantics
   structure Sequent = Sequent
   structure Development = Development
   structure Builtins = Builtins)
