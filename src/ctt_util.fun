functor CttUtil
  (structure Lcf : LCF_APART
   structure Ctt : CTT where Lcf = Lcf) : CTT_UTIL =
struct
  structure Lcf = Lcf
  structure Tacticals = ProgressTacticals(Lcf)
  open Ctt Ctt.ConvTypes

  structure Conversionals = Conversionals
    (structure Syntax = Syntax
     structure ConvTypes = ConvTypes)

  open Tacticals Rules
  infix ORELSE THEN

  local
    val EqRules =
      AxEq
      ORELSE EqEq
      ORELSE FunEq NONE
      ORELSE IsectEq NONE
      ORELSE PairEq (NONE, NONE)
      ORELSE LamEq (NONE, NONE)
      ORELSE UnitEq
      ORELSE ProdEq NONE
      ORELSE VoidEq
      ORELSE UnivEq
      ORELSE HypEq
      ORELSE ApEq NONE
      ORELSE SpreadEq (NONE, NONE, NONE)
      ORELSE Cum NONE
      ORELSE SubsetEq NONE
      ORELSE SubsetMemberEq (NONE, NONE)
      ORELSE IsectMemberEq (NONE, NONE)

    val IntroRules =
      MemUnfold
      ORELSE Assumption
      ORELSE FunIntro (NONE, NONE)
      ORELSE IsectIntro (NONE, NONE)
      ORELSE UnitIntro

    open Conversions Conversionals
    infix CORELSE

    val Reduce = ApBeta CORELSE SpreadBeta
    val DeepReduce = RewriteGoal (CDEEP Reduce)
  in
    val Auto =
      LIMIT (IntroRules ORELSE EqRules ORELSE PROGRESS DeepReduce)
  end
end

structure CttUtil = CttUtil
  (structure Lcf = Lcf and Ctt = Ctt)
