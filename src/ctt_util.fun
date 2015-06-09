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

  type intro_args =
    {term : term option,
     fresh_variable : name option,
     level : Level.t option}

  type elim_args =
    {target : name,
     names : name list,
     term : term option}

  fun Intro {term,fresh_variable,level} =
     MemCD
       ORELSE UnitIntro
       ORELSE Assumption
       ORELSE FunIntro (fresh_variable, level)
       ORELSE IsectIntro (fresh_variable, level)
       ORELSE_LAZY (fn _ => ProdIntro (valOf term, fresh_variable, level))
       ORELSE_LAZY (fn _ => SubsetIntro (valOf term, fresh_variable, level))

  fun take2 (x::y::_) = SOME (x,y)
    | take2 _ = NONE

  fun Elim {target, names, term} =
    (VoidElim THEN Hypothesis target)
      ORELSE UnitElim target
      ORELSE ProdElim (target, take2 names)
      ORELSE_LAZY (fn _ => FunElim (target, valOf term, take2 names))
      ORELSE_LAZY (fn _ => IsectElim (target, valOf term, take2 names))
      ORELSE SubsetElim (target, take2 names)

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

    val AutoVoidElim = VoidElim THEN Assumption
    val AutoIntro = Intro {term = NONE, fresh_variable = NONE, level = NONE}

    open Conversions Conversionals
    infix CORELSE

    val Reduce = ApBeta CORELSE SpreadBeta
    val DeepReduce = RewriteGoal (CDEEP Reduce)
  in
    val Auto =
      LIMIT (AutoIntro ORELSE AutoVoidElim ORELSE EqRules ORELSE PROGRESS DeepReduce)
  end
end

structure CttUtil = CttUtil
  (structure Lcf = Lcf and Ctt = Ctt)
