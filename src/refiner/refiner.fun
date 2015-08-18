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

    open Utils
    open Goal Sequent Syntax CttCalculus Derivation

    infix $ \ BY ^!
    infix 3 >>
    infix 2 |:
    infix 8 $$ // @@
    infixr 8 \\

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

    local
      open CttCalculusView
      datatype ForallType = ForallIsect | ForallFun
      structure Tacticals = Tacticals (Lcf)
      open Tacticals
      infix THEN THENL
    in
      fun stripForalls (H, P) =
        case project P of
             ISECT $ #[A, xB] =>
               let
                 val (H', x, B) = ctxUnbind (H, A, xB)
                 val (xs, Q) = stripForalls (H', B)
               in
                 (xs @ [(ForallIsect, x)], Q)
               end
           | FUN $ #[A, xB] =>
               let
                 val (H', x, B) = ctxUnbind (H, A, xB)
                 val (xs, Q) = stripForalls (H', B)
               in
                 (xs @ [(ForallFun, x)], Q)
               end
           | _ => ([], P)

      fun BHyp hyp (goal as _ |: (sequent as H >> P)) =
        let
          val target = eliminationTarget hyp sequent

          val (variables, Q) = stripForalls (H, Context.lookup H target)
          val fvs = List.map #1 (Context.listItems H)
          val solution = Unify.unify (Meta.convertFree fvs Q, Meta.convertFree fvs P)

          val instantiations = List.map (fn (ty, v) => (ty, Unify.Solution.lookup solution v)) variables

          val targetRef = ref target
          fun go [] = ID
            | go ((ty, e) :: es) = fn goal' as _ |: H' >> _ =>
              let
                val currentTarget = Context.rebindName H' (! targetRef)
                val nextTarget = Variable.prime currentTarget
                val _ = targetRef := nextTarget
                val instantiation = Meta.unconvert (fn _ => raise Refine) e
                val eqName = Context.fresh (H', Variable.named "_")
                val names = (nextTarget, eqName)
                val hyp = HypSyn.NAME currentTarget
                val elim =
                  case ty of
                       ForallIsect => IsectElim
                     | ForallFun => FunElim
                val tac =
                  elim (hyp, instantiation, SOME names)
                    THEN Thin hyp
              in
                (tac THENL [ID, go es]) goal'
              end
        in
          go (rev instantiations) goal
        end
    end
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
