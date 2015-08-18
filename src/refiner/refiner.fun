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
    open UnivRules

    structure EqRules = EqRules(Utils)
    open EqRules

    structure FunRules = FunRules(Utils)
    open FunRules

    structure ISectRules = ISectRules(Utils)
    open ISectRules

    structure SubsetRules = SubsetRules(Utils)
    open SubsetRules

    structure NatRules = NatRules(Utils)
    open NatRules

    structure BaseRules = BaseRules(Utils)
    open BaseRules

    structure ImageRules = ImageRules(Utils)
    open ImageRules

    structure GeneralRules = GeneralRules(Utils)
    open GeneralRules

    structure ProdRules = ProdRules(Utils)
    open ProdRules

    structure PlusRules = PlusRules(Utils)
    open PlusRules

    structure AtomRules = AtomRules(Utils)
    open AtomRules

    structure CEqRules = CEqRules(Utils)
    open CEqRules

    structure ApproxRules = ApproxRules(Utils)
    open ApproxRules

    (* BHyp gets its own special functor because it depends
     * on a number of other tactics.
     *)
    structure BHypRules = BHypRules
     (structure U = Utils
      val FunElim = FunElim
      val IsectElim = IsectElim
      val Thin = Thin)
    open BHypRules
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
