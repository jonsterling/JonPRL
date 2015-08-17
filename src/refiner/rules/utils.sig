signature RULES_UTIL_INPUT =
sig
  structure Syntax : ABT_UTIL
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
    where type Conv.term = Conv.term

  exception Refine
end

signature RULES_UTIL =
sig
  include RULES_UTIL_INPUT

  type tactic = Lcf.tactic
  type conv = Conv.conv
  type name = Sequent.name
  type term = Syntax.t

  type operator = Syntax.Operator.t
  type hyp = name HypSyn.t
  type world = Development.world

  structure CttCalculusView :
    sig
      datatype 'a view =
          $ of CttCalculusInj.t * 'a vector
        | \ of Syntax.Variable.t * 'a
        | ` of Syntax.Variable.t

      val inject : Syntax.t view -> Syntax.t
      val project : Syntax.t -> Syntax.t view
    end

  structure Conversionals : CONVERSIONALS
    where type conv = Conv.conv

  structure C : INJECTION
    where type t = CttCalculus.t
    where type ambient = Syntax.Operator.t
  structure D : INJECTION
    where type t = Derivation.t
    where type ambient = Syntax.Operator.t

  structure Meta : META_CONVERT
    where A = Syntax
  structure MetaAbt : ABT_UTIL
    where Operator = Meta.MetaOperator
    where Variable = Syntax.Variable
  structure Unify : UNIFY
    where type t = MetaAbt.t
    where type var = MetaAbt.Variable.t

  val applySolution : Unify.solution -> MetaAbt.t -> Syntax.t

  structure Context : CONTEXT

  val ctxSubst : Sequent.context
                 -> term
                 -> Sequent.Context.name
                 -> Sequent.Context.context
  val ctxUnbind : Sequent.context * term * term
                  -> Sequent.Context.context * Sequent.Context.name * term

  val assertClosed : Sequent.context -> term -> unit

  val mkEvidence : Derivation.t -> term list -> term
  val BY : 'a * 'b -> 'a * 'b

  val @@ : Sequent.Context.context *
           (Sequent.Context.name * Sequent.Context.term)
           -> Sequent.Context.context

  val asApp : term -> CttCalculus.t * term vector
  val ^! : term * CttCalculus.t -> term vector
  val asVariable : term -> Syntax.Variable.t

  val unify : term -> term -> term
  val assertSubtype_ : (Sequent.context
                       -> term -> term -> term)
                       -> Sequent.context
                       -> term -> term -> term
  val typeLub : Sequent.context -> term -> term -> term

  val operatorIrrelevant : CttCalculus.t -> bool
  val assertIrrelevant : 'a * term -> unit

  val eliminationTarget : Sequent.Context.name HypSyn.t
                          -> Sequent.sequent
                          -> Sequent.Context.name

  val inferLevel : Sequent.context * term -> Level.t
  val inferType : Sequent.context * term -> term

  val QuantifierEq : CttCalculus.t * Derivation.t
                     -> Syntax.Variable.t option -> tactic

  val Hypothesis_ : Syntax.Variable.t -> tactic
end
