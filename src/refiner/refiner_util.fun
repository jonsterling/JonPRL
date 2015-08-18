functor RefinerUtil
  (structure Syntax : ABT
     where type Operator.t = UniversalOperator.t
   structure Sequent : SEQUENT
     where type term = Syntax.t
     where Context.Syntax = Syntax
   structure Lcf : LCF_APART
     where type evidence = Syntax.t
     where type goal = Sequent.sequent Goal.goal
   structure Conv : CONV
     where type term = Syntax.t
   structure Refiner : REFINER
      where type tactic = Lcf.tactic
      where type conv = Conv.conv
      where type term = Syntax.t
      where type name = Syntax.Variable.t
      where type operator = Syntax.Operator.t
      where type Sequent.sequent = Sequent.sequent) : REFINER_UTIL =
struct
  structure Lcf = Lcf
  structure Tacticals = ProgressTacticals(Lcf)
  open Conv Refiner

  structure Conversionals = Conversionals
    (structure Syntax = Syntax
     structure Conv = Conv)

  open Tacticals Rules
  infix ORELSE ORELSE_LAZY THEN

  type intro_args =
    {term : term option,
     invertible : bool,
     rule : int option,
     freshVariable : name option,
     level : Level.t option}

  type elim_args =
    {target : hyp,
     names : name list,
     term : term option}

  type eq_cd_args =
    {names : name list,
     invertible : bool,
     level : Level.t option,
     terms : term list}

  type ext_args =
    {freshVariable : name option,
     level : Level.t option}

  type match_args =
    {hyps   : (name * term) list,
     goal   : term,
     branch : (name * term) list -> tactic} list

  val CEqRefl = CEqRules.CEqApprox THEN ApproxRules.ApproxRefl

  local
    structure Tacticals = Tacticals (Lcf)
    open Tacticals Goal Sequent Syntax
    infix THENL
    infix 3 >> infix 2 |:
    infix $
  in
    fun OnClass cls tac (goal as cls' |: _) =
      if cls = cls' then
        tac goal
      else
        ID goal

    fun UnfoldHead world (goal as _ |: H >> P) =
      case out P of
           theta $ _ => GeneralRules.Unfolds (world, [(theta, NONE)]) goal
         | _ => raise Refine

    fun CutLemma (world, theta : operator) =
      let
        val {statement,...} = Development.lookupTheorem world theta
        val H >> P = statement
        val _ = if Context.eq (H, Context.empty) then () else raise Fail "nonempty context"
        val name = Syntax.Variable.named (Syntax.Operator.toString theta)
      in
        GeneralRules.Assert (P, SOME name)
          THENL [GeneralRules.Lemma (world, theta), ID]
      end
  end


  (* VR: Intro should try to unfold abstractions *)
  fun Intro {term,rule,invertible,freshVariable,level} =
       GeneralRules.Assumption
       ORELSE_LAZY (fn _ => case valOf rule of
                                0 => PlusRules.PlusIntroL level
                              | 1 => PlusRules.PlusIntroR level
                              | _ => raise Fail "Out of range for PLUS")
       ORELSE FunRules.Intro (freshVariable, level)
       ORELSE ISectRules.Intro (freshVariable, level)
       ORELSE_LAZY (fn _ => ProdRules.ProdIntro (valOf term, freshVariable, level))
       ORELSE ProdRules.IndependentProdIntro
       ORELSE_LAZY (fn _ => SubsetRules.Intro (valOf term, freshVariable, level))
       ORELSE SubsetRules.IndependentIntro
       ORELSE CEqRefl
       ORELSE ApproxRules.ApproxRefl
       ORELSE BaseRules.Intro
       ORELSE
       (if not invertible then
            CEqRules.CEqStruct
        else
            FAIL)

  fun ReduceEquand dir =
    case dir of
         Dir.LEFT => AtomRules.TestAtomReduceLeft
       | Dir.RIGHT => AtomRules.TestAtomReduceRight

  fun take2 (x::y::_) = SOME (x,y)
    | take2 _ = NONE

  fun take3 (x::y::z::_) = SOME (x,y,z)
    | take3 _ = NONE

  fun take4 (u::v::w::x::_) = SOME (u,v,w,x)
    | take4 _ = NONE

  fun listAt (xs, n) = SOME (List.nth (xs, n)) handle _ => NONE

  local
    structure AbtUtil = AbtUtil (Syntax)
    structure CI = CttCalculusInj
    structure C = CttCalculus

    open Goal Sequent AbtUtil
    open Conversions Conversionals

    val DeepReduce = GeneralRules.RewriteGoal (CDEEP Step)

    infix THENL
    infix 3 >> infix 2 |:
    infix 8 $$
    infixr 8 \\
  in
    fun UnitEq world =
      COMPLETE
        (GeneralRules.Unfolds (world, [(CI.`> C.UNIT, NONE)])
          THEN ApproxRules.ApproxEq
          THEN BaseRules.MemberEq
          THEN CEqRules.CEqApprox
          THEN ApproxRules.ApproxRefl)

    fun UnitMemEq world =
      COMPLETE
        (GeneralRules.Unfolds (world, [(CI.`> C.UNIT, NONE)])
          THEN ApproxRules.ApproxMemEq
          THEN ApproxRules.ApproxRefl)

    fun VoidElim world =
      let
        val oprv  = CI.`> C.VOID
        val oprb  = CI.`> C.BOT
        val oprh  = CI.`> C.HASVALUE
        val opri  = CI.`> C.ID
        val oprm  = CI.`> C.MEM
        val namex = Variable.named "x"
        val nameh = Variable.named "h"
        val nameq = Variable.named "q"
        val namev = Variable.named "v"
        val void  = oprv $$ #[]
        val bot   = oprb $$ #[]
        val ax    = CI.`> C.AX $$ #[]
        val hv    = oprh $$ #[bot]
        val ceq   = CI.`> C.CEQUAL $$ #[bot, ax]
        val hvx   = oprh $$ #[``namex]
        val xC    = namex \\ hvx
      in
        (GeneralRules.Assert (void, SOME nameh) THENL
          [ID,
           GeneralRules.Unfolds (world, [(oprv, NONE)])
            THEN GeneralRules.Assert (hv, SOME nameq) THENL
              [CEqRules.CEqSubst (ceq, xC) THENL
                [CEqRules.CEqApprox THENL
                  [ApproxRules.AssumeHasValue (SOME namev, NONE) THENL
                    [ApproxRules.BottomDiverges (HypSyn.NAME namev),
                     GeneralRules.Unfolds (world, [(oprh, NONE),(oprb, NONE),(oprm, NONE),(opri, NONE)])
                       THEN ApproxRules.ApproxEq
                       THEN BaseRules.MemberEq
                       THEN CEqRules.CEqApprox
                       THEN ApproxRules.ApproxRefl],
                   GeneralRules.Assumption],
                 GeneralRules.Unfolds (world, [(oprh, NONE)]) THEN DeepReduce THEN ApproxRules.ApproxRefl],
               ApproxRules.BottomDiverges (HypSyn.NAME nameq)]])
      end

    fun VoidEq world =
      let val oprv  = CI.`> C.VOID
      in GeneralRules.Unfolds (world, [(oprv, NONE)])
         THEN ApproxRules.ApproxEq
         THEN BaseRules.MemberEq
         THEN CEqRules.CEqApprox
         THEN ApproxRules.ApproxRefl
      end
  end

  fun Elim {target, names, term} world =
    let
      val twoNames = take2 names
      val fourNames = take4 names
    in
      (VoidElim world THEN GeneralRules.Hypothesis target)
        ORELSE ApproxRules.ApproxElim target
        ORELSE_LAZY (fn _ => BaseRules.ElimEq (target, listAt (names, 0)))
        ORELSE_LAZY (fn _ => PlusRules.PlusElim (target, twoNames))
        ORELSE_LAZY (fn _ => ProdRules.ProdElim (target, twoNames))
        ORELSE_LAZY (fn _ => FunRules.Elim (target, valOf term, twoNames))
        ORELSE_LAZY (fn _ => ISectRules.Elim (target, valOf term, twoNames))
        ORELSE ImageRules.ImageEqInd (target, fourNames)
        ORELSE ImageRules.ImageElim (target, listAt (names, 0))
        ORELSE NatRules.Elim (target, twoNames)
        ORELSE SubsetRules.Elim (target, twoNames)
    end

  fun EqCD {names, level, invertible, terms} world =
    let
      val freshVariable = listAt (names, 0)
    in
      EqRules.Eq
        ORELSE AtomRules.AtomEq
        ORELSE AtomRules.TokenEq
        ORELSE AtomRules.MatchTokenEq
        ORELSE AtomRules.TestAtomEq freshVariable
        ORELSE UnitEq world
        ORELSE UnitMemEq world
        ORELSE EqRules.MemEq
        ORELSE CEqRules.CEqEq
        ORELSE CEqRules.CEqMemEq
        ORELSE ApproxRules.ApproxEq
        ORELSE ApproxRules.ApproxMemEq
        ORELSE VoidEq world
        ORELSE GeneralRules.HypEq
        ORELSE UnivRules.Eq
        ORELSE PlusRules.PlusEq
        ORELSE PlusRules.InlEq level
        ORELSE PlusRules.InrEq level
        ORELSE BaseRules.Eq
        ORELSE BaseRules.MemberEq
        ORELSE FunRules.Eq freshVariable
        ORELSE ISectRules.Eq freshVariable
        ORELSE ProdRules.ProdEq freshVariable
        ORELSE SubsetRules.Eq freshVariable
        ORELSE ProdRules.PairEq (freshVariable, level)
        ORELSE FunRules.LamEq (freshVariable, level)
        ORELSE SubsetRules.MemberEq (freshVariable, level)
        ORELSE ISectRules.MemberEq (freshVariable, level)
        ORELSE_LAZY (fn _ =>
          case terms of
               [M, N] => ISectRules.MemberCaseEq (SOME M, N)
             | [N] => ISectRules.MemberCaseEq (NONE, N)
             | _ => FAIL)
        ORELSE NatRules.Eq
        ORELSE NatRules.ZeroEq
        ORELSE NatRules.SuccEq
        ORELSE UnivRules.Cum level
        ORELSE SubsetRules.EqInSupertype
        ORELSE ImageRules.ImageEq
        ORELSE ImageRules.ImageMemEq
        ORELSE
        (if not invertible then
             NatRules.RecEq (listAt (terms, 0), take2 names)
               ORELSE_LAZY (fn _ => PlusRules.DecideEq (List.nth (terms, 0))
                                                       (List.nth (terms, 1),
                                                        List.nth (terms, 2),
                                                        take3 names))
               ORELSE ProdRules.SpreadEq (listAt (terms, 0), listAt (terms, 1), take3 names)
               ORELSE FunRules.ApEq (listAt (terms, 0))
         else
             FAIL)

    end

  fun Ext {freshVariable, level} =
    FunRules.FunExt (freshVariable, level)
    ORELSE ApproxRules.ApproxExtEq

  fun Match [] = FAIL
    | Match [{hyps, goal, branch}] = GeneralRules.MatchSingle (hyps, goal, branch)
    | Match ({hyps, goal, branch} :: branches) =
      GeneralRules.MatchSingle (hyps, goal, branch)
      ORELSE_LAZY (fn () => Match branches)

  local
    fun InvAutoEqCD world = EqCD {names = [],
                                  level = NONE,
                                  invertible = true,
                                  terms = []} world
    fun AutoEqCD world = EqCD {names = [],
                              level = NONE,
                              invertible = false,
                              terms = []} world

    fun AutoVoidElim world = VoidElim world THEN GeneralRules.Assumption

    val InvAutoIntro = Intro {term = NONE,
                              rule = NONE,
                              invertible = true,
                              freshVariable = NONE,
                              level = NONE}
    val AutoIntro = Intro {term = NONE,
                           rule = NONE,
                           invertible = false,
                           freshVariable = NONE,
                           level = NONE}

    open Conversions Conversionals
    infix CORELSE

    val DeepReduce = GeneralRules.RewriteGoal (CDEEP Step)
  in
    fun FinAuto (wld, 0) = LIMIT (UnfoldHead wld ORELSE InvAutoIntro ORELSE AutoVoidElim wld ORELSE InvAutoEqCD wld)
      | FinAuto (wld, n) = FinAuto (wld, 0) THEN (AutoIntro ORELSE AutoEqCD wld) THEN FinAuto (wld, n - 1)

    fun InfAuto wld = LIMIT (UnfoldHead wld ORELSE AutoIntro ORELSE AutoVoidElim wld ORELSE AutoEqCD wld)

    fun Auto (wld, opt) =
      case opt of
           NONE => InfAuto wld
         | SOME n => FinAuto (wld, n)

    fun Reduce NONE = LIMIT DeepReduce
      | Reduce (SOME n) =
        let
          fun go 0 = ID
            | go n = DeepReduce THEN (go (n - 1))
        in
          go n
        end
  end
end

structure RefinerUtil = RefinerUtil
  (structure Syntax = Syntax and Sequent = Sequent and Lcf = Lcf and Conv = Conv and Refiner = Refiner)
