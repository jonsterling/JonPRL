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
  infix ORELSE ORELSE_LAZY THEN

  local
    val EqRules =
      AxEq
      ORELSE EqEq
      ORELSE FunEq NONE
      ORELSE IsectEq NONE
      ORELSE PairEq NONE NONE
      ORELSE LamEq NONE NONE
      ORELSE UnitEq
      ORELSE ProdEq NONE
      ORELSE VoidEq
      ORELSE UnivEq
      ORELSE HypEq
      ORELSE ApEq NONE
      ORELSE SpreadEq NONE NONE NONE
      ORELSE Cum NONE
      ORELSE SubsetEq NONE
      ORELSE SubsetMemberEq NONE NONE

    val IntroRules =
      MemUnfold
      ORELSE Assumption
      ORELSE FunIntro NONE NONE
      ORELSE IsectIntro NONE NONE
      ORELSE UnitIntro

    open Conversions Conversionals
    infix CORELSE

    val Reduce = ApBeta CORELSE SpreadBeta
  in
    val DeepReduce = RewriteGoal (CDEEP Reduce)
    val Auto =
      LIMIT (PROGRESS DeepReduce ORELSE IntroRules ORELSE EqRules)
  end
end

structure CttUtil = CttUtil
  (structure Lcf = Lcf and Ctt = Ctt)
