functor CttUtil
  (structure Lcf : LCF_APART
   structure Ctt : CTT
     where type tactic = Lcf.tactic
     where type conv = ConvTypes.conv
   structure ConvTypes : CONV_TYPES where Syntax = Syntax) : CTT_UTIL =
struct
  open Ctt

  structure Tacticals = ProgressTacticals(Lcf)
  structure Conversionals = Conversionals
    (structure Syntax = Syntax
     structure ConvTypes = ConvTypes)

  open Tacticals Rules
  open Rules
  infix ORELSE ORELSE_LAZY THEN

  local
    val EqAuto =
      AxEq
      ORELSE EqEq
      ORELSE SquashEq
      ORELSE FunEq NONE
      ORELSE IsectEq NONE
      ORELSE PairEq NONE NONE
      ORELSE LamEq NONE NONE
      ORELSE UnitEq
      ORELSE ProdEq NONE
      ORELSE VoidEq
      ORELSE UnivEq
      ORELSE SquashEq
      ORELSE HypEq
      ORELSE Cum NONE

    val intro_rules =
      MemUnfold
      ORELSE EqAuto
      ORELSE Assumption
      ORELSE FunIntro NONE NONE
      ORELSE IsectIntro NONE NONE
      ORELSE UnitIntro
      ORELSE SquashIntro

    val elim_rules =
      ApEq NONE
      ORELSE SpreadEq NONE NONE NONE

    open Conversions Conversionals
    infix CORELSE

    val whnf = ApBeta CORELSE SpreadBeta
    val DeepReduce = RewriteGoal (CDEEP whnf)
    val IntroElim = intro_rules ORELSE elim_rules
  in
    val Auto =
      LIMIT (IntroElim ORELSE PROGRESS DeepReduce)
  end
end

structure CttUtil = CttUtil
  (structure Lcf = Lcf
   structure ConvTypes = ConvTypes
   structure Ctt = Ctt)
