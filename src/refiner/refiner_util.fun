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
  structure Tacticals = Tacticals(Lcf)
  structure ProgressTacticals = ProgressTacticals(Lcf)
  open Conv Refiner

  structure Conversionals = Conversionals
    (structure Syntax = Syntax
     structure Conv = Conv)

  open ProgressTacticals Tacticals Rules
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

  val CEqRefl = CEqRules.Approx THEN ApproxRules.Refl

  local
    open Goal Sequent Syntax
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

    fun CutLemma (world, theta : operator, oname) =
      let
        val {statement,...} = Development.lookupTheorem world theta
        val H >> P = statement
        val _ = if Context.eq (H, Context.empty) then () else raise Fail "nonempty context"
        val name = case oname of SOME name => name | NONE => Syntax.Variable.named (Syntax.Operator.toString theta)
      in
        GeneralRules.Assert (P, SOME name)
          THENL [GeneralRules.Lemma (world, theta), ID]
      end

    structure CttCalculusView = RestrictAbtView
      (structure Abt = Syntax and Injection = CttCalculusInj)

    fun WfLemma (world, theta : operator) =
      let
        val name = Syntax.Variable.named (Syntax.Operator.toString theta)
        val hyp = HypSyn.NAME name
        val cutWfLemma = CutLemma (world, theta, SOME name)
        val useHyp = GeneralRules.Hypothesis hyp ORELSE BHypRules.BHyp hyp
        open CttCalculusInj CttCalculus CttCalculusView
      in
        fn goal as (_ |: H >> P) =>
          (case project P of
               MEM $ _ => cutWfLemma THEN useHyp
             | EQ $ _ => cutWfLemma THEN GeneralRules.Unfolds (world, [(`> MEM, NONE)]) THEN useHyp
             | _ => FAIL) goal
      end
  end

  (* VR: Intro should try to unfold abstractions *)
  fun Intro {term,rule,invertible,freshVariable,level} D =
       GeneralRules.Assumption
       ORELSE_LAZY (fn _ => case valOf rule of
                                0 => PlusRules.IntroL level
                              | 1 => PlusRules.IntroR level
                              | _ => raise Fail "Out of range for PLUS")
       ORELSE FunRules.Intro (freshVariable, level)
       ORELSE ISectRules.Intro (freshVariable, level)
       ORELSE_LAZY (fn _ => ProdRules.Intro (valOf term, freshVariable, level))
       ORELSE ProdRules.IndependentIntro
       ORELSE_LAZY (fn _ => SubsetRules.Intro (valOf term, freshVariable, level))
       ORELSE SubsetRules.IndependentIntro
       ORELSE CEqRefl
       ORELSE ApproxRules.Refl
       ORELSE BaseRules.Intro
       ORELSE WTreeRules.Intro
       ORELSE
       (if not invertible then
            CEqRules.Struct
        else
            ID)
       ORELSE List.foldl (fn (t, ts) => PROGRESS t ORELSE ts) FAIL
                (Development.lookupResource D Resource.INTRO)

  fun ReduceEquand dir =
    case dir of
         Dir.LEFT => AtomRules.TestReduceLeft
       | Dir.RIGHT => AtomRules.TestReduceRight

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
          THEN ApproxRules.Eq
          THEN BaseRules.MemberEq
          THEN CEqRules.Approx
          THEN ApproxRules.Refl)

    fun UnitMemEq world =
      COMPLETE
        (GeneralRules.Unfolds (world, [(CI.`> C.UNIT, NONE)])
          THEN ApproxRules.MemEq
          THEN ApproxRules.Refl)

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
              [CEqRules.Subst (ceq, SOME xC) THENL
                [CEqRules.Approx THENL
                  [ApproxRules.AssumeHasValue (SOME namev, NONE) THENL
                    [ApproxRules.BottomDiverges (HypSyn.NAME namev),
                     GeneralRules.Unfolds (world, [(oprh, NONE),(oprb, NONE),(oprm, NONE),(opri, NONE)])
                       THEN ApproxRules.Eq
                       THEN BaseRules.MemberEq
                       THEN CEqRules.Approx
                       THEN ApproxRules.Refl],
                   GeneralRules.Assumption],
                 GeneralRules.Unfolds (world, [(oprh, NONE)]) THEN DeepReduce THEN ApproxRules.Refl],
               ApproxRules.BottomDiverges (HypSyn.NAME nameq)]])
      end

    fun VoidEq world =
      let val oprv  = CI.`> C.VOID
      in GeneralRules.Unfolds (world, [(oprv, NONE)])
         THEN ApproxRules.Eq
         THEN BaseRules.MemberEq
         THEN CEqRules.Approx
         THEN ApproxRules.Refl
      end
  end

  fun Elim {target, names, term} world =
    let
      val twoNames = take2 names
      val threeNames = take3 names
      val fourNames = take4 names
    in
      (VoidElim world THEN GeneralRules.Hypothesis target)
        ORELSE ApproxRules.Elim target
        ORELSE_LAZY (fn _ => BaseRules.ElimEq (target, listAt (names, 0)))
        ORELSE_LAZY (fn _ => PlusRules.Elim (target, twoNames))
        ORELSE_LAZY (fn _ => ProdRules.Elim (target, twoNames))
        ORELSE_LAZY (fn _ => ContainerRules.Elim (target, twoNames))
        ORELSE_LAZY (fn _ => ContainerExtensionRules.Elim (target, twoNames))
        ORELSE_LAZY (fn _ => NeighborhoodRules.Elim (target, threeNames))
        ORELSE_LAZY (fn _ => FunRules.Elim (target, valOf term, twoNames))
        ORELSE_LAZY (fn _ => ISectRules.Elim (target, valOf term, twoNames))
        ORELSE ImageRules.EqInd (target, fourNames)
        ORELSE ImageRules.Elim (target, listAt (names, 0))
        ORELSE NatRules.Elim (target, twoNames)
        ORELSE SubsetRules.Elim (target, twoNames)
        ORELSE WTreeRules.Elim (target, threeNames)
        ORELSE CEqRules.Elim (target, twoNames)
        ORELSE List.foldl (fn (t, ts) => PROGRESS t ORELSE ts) FAIL
                 (Development.lookupResource world Resource.ELIM)
    end

  fun EqCD {names, level, invertible, terms} world =
    let
      val freshVariable = listAt (names, 0)
    in
      EqRules.Eq
        ORELSE AtomRules.Eq
        ORELSE AtomRules.TokenEq
        ORELSE AtomRules.MatchTokenEq
        ORELSE AtomRules.TestEq freshVariable
        ORELSE UnitEq world
        ORELSE UnitMemEq world
        ORELSE EqRules.MemEq
        ORELSE CEqRules.Eq
        ORELSE CEqRules.MemEq
        ORELSE ApproxRules.Eq
        ORELSE ApproxRules.MemEq
        ORELSE VoidEq world
        ORELSE GeneralRules.HypEq
        ORELSE UnivRules.Eq
        ORELSE PlusRules.Eq
        ORELSE PlusRules.InlEq level
        ORELSE PlusRules.InrEq level
        ORELSE BaseRules.Eq
        ORELSE BaseRules.MemberEq
        ORELSE FunRules.Eq freshVariable
        ORELSE ISectRules.Eq freshVariable
        ORELSE ProdRules.Eq freshVariable
        ORELSE SubsetRules.Eq freshVariable
        ORELSE ProdRules.MemEq (freshVariable, level)
        ORELSE FunRules.LamEq (freshVariable, level)
        ORELSE SubsetRules.MemberEq (freshVariable, level)
        ORELSE ISectRules.MemberEq (freshVariable, level)
        ORELSE ContainerRules.Eq
        ORELSE ContainerRules.MemEq
        ORELSE ContainerExtensionRules.Eq
        ORELSE ContainerExtensionRules.MemEq
        ORELSE NeighborhoodRules.Eq
        ORELSE NeighborhoodRules.MemEq level
        ORELSE_LAZY (fn _ =>
          case terms of
               [M, N] => ISectRules.MemberCaseEq (SOME M, N)
             | [N] => ISectRules.MemberCaseEq (NONE, N)
             | _ => FAIL)
        ORELSE_LAZY (fn _ =>
          case terms of
               [M, N] => WTreeRules.RecEq (SOME M, N)
             | [N] => WTreeRules.RecEq (NONE, N)
             | _ => FAIL)
        ORELSE NatRules.Eq
        ORELSE NatRules.ZeroEq
        ORELSE NatRules.SuccEq
        ORELSE UnivRules.Cum level
        ORELSE SubsetRules.EqInSupertype
        ORELSE ImageRules.Eq
        ORELSE ImageRules.MemEq
        ORELSE WTreeRules.Eq
        ORELSE WTreeRules.MemEq
        ORELSE
        (if not invertible then
             NatRules.RecEq (listAt (terms, 0), take2 names)
               ORELSE_LAZY (fn _ => PlusRules.DecideEq (List.nth (terms, 0),
                                                        List.nth (terms, 1),
                                                        take3 names))
               ORELSE ProdRules.SpreadEq (listAt (terms, 0), listAt (terms, 1), take3 names)
               ORELSE NeighborhoodRules.IndEq (listAt (terms, 0), listAt (terms, 1), take3 names)
               ORELSE FunRules.ApEq (listAt (terms, 0))
         else
             ID)
        ORELSE List.foldl (fn (t, ts) => PROGRESS t ORELSE ts) FAIL
                 (Development.lookupResource world Resource.EQ_CD)

    end

  fun Ext {freshVariable, level} =
    FunRules.FunExt (freshVariable, level)
    ORELSE ApproxRules.ExtEq

  fun Wf world =
    List.foldl
     (fn (t, ts) => PROGRESS t ORELSE ts)
     FAIL
     (Development.lookupResource world Resource.WF)

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
    fun FinAuto (wld, 0) =
      LIMIT (UnfoldHead wld
             ORELSE InvAutoIntro wld
             ORELSE AutoVoidElim wld
             ORELSE InvAutoEqCD wld
             ORELSE List.foldl (fn (t, ts) => PROGRESS t ORELSE ts) ID
                      (Development.lookupResource wld Resource.AUTO))
      | FinAuto (wld, n) =
        FinAuto (wld, 0)
        THEN (AutoIntro wld
              ORELSE AutoEqCD wld
              ORELSE Wf wld
              ORELSE List.foldl (fn (t, ts) => PROGRESS t ORELSE ts) ID (Development.lookupResource wld Resource.AUTO))
        THEN FinAuto (wld, n - 1)

    fun InfAuto wld =
      LIMIT (UnfoldHead wld
             ORELSE AutoIntro wld
             ORELSE AutoVoidElim wld
             ORELSE AutoEqCD wld
             ORELSE Wf wld
             ORELSE List.foldl (fn (t, ts) => PROGRESS t ORELSE ts) ID (Development.lookupResource wld Resource.AUTO))

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
