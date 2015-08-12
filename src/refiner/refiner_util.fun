functor RefinerUtil
  (structure Lcf : LCF_APART
   structure Syntax : ABT where type Operator.t = UniversalOperator.t
   structure Conv : CONV
     where type term = Syntax.t
   structure Refiner : REFINER
      where type tactic = Lcf.tactic
      where type conv = Conv.conv
      where type term = Syntax.t
      where type name = Syntax.Variable.t
      where type operator = Syntax.Operator.t
   sharing type Lcf.goal = Refiner.Sequent.sequent) : REFINER_UTIL =
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

  val CEqRefl = CEqApprox THEN ApproxRefl

  local
    structure Tacticals = Tacticals (Lcf)
    open Tacticals Sequent Syntax
    infix THENL >>
    infix $
  in
    fun UnfoldHead world (goal as H >> P) =
      case out P of
           theta $ _ => Unfolds (world, [(theta, NONE)]) goal
         | _ => raise Refine

    fun CutLemma (world, theta : operator) =
      let
        val {statement,...} = Development.lookupTheorem world theta
        val H >> P = statement
        val _ = if Context.eq (H, Context.empty) then () else raise Fail "nonempty context"
        val name = Syntax.Variable.named (Syntax.Operator.toString theta)
      in
        Assert (P, SOME name)
          THENL [Lemma (world, theta), ID]
      end
  end


  (* VR: Intro should try to unfold abstractions *)
  fun Intro {term,rule,invertible,freshVariable,level} =
     (*UnitIntro
       ORELSE*) Assumption
       ORELSE_LAZY (fn _ => case valOf rule of
                                0 => PlusIntroL level
                              | 1 => PlusIntroR level
                              | _ => raise Fail "Out of range for PLUS")
       ORELSE FunIntro (freshVariable, level)
       ORELSE IsectIntro (freshVariable, level)
       ORELSE_LAZY (fn _ => ProdIntro (valOf term, freshVariable, level))
       ORELSE IndependentProdIntro
       ORELSE_LAZY (fn _ => SubsetIntro (valOf term, freshVariable, level))
       ORELSE IndependentSubsetIntro
       ORELSE CEqRefl
       ORELSE ApproxRefl
       ORELSE BaseIntro
       ORELSE
       (if not invertible then
            CEqStruct
        else
            FAIL)

  fun take2 (x::y::_) = SOME (x,y)
    | take2 _ = NONE

  fun take3 (x::y::z::_) = SOME (x,y,z)
    | take3 _ = NONE

  fun take4 (u::v::w::x::_) = SOME (u,v,w,x)
    | take4 _ = NONE

  fun listAt (xs, n) = SOME (List.nth (xs, n)) handle _ => NONE

  local
      (*structure Tacticals = Tacticals (Lcf)*)
      structure AbtUtil = AbtUtil (Syntax)
      structure CI = CttCalculusInj
      structure C = CttCalculus
      open (*Tacticals*) Sequent AbtUtil (*Syntax*)
      infix THENL >>
      infix 8 $$
  in
  fun VoidElim world (goal as H >> P) =
    let val oprv = CI.`> C.VOID
	val void = oprv $$ #[]
        val name = Variable.named "v"
    in (Assert (void, SOME name)
               THENL [ ID
		     , Unfolds (world, [(oprv, NONE)])
       ]) goal
    end
(*
  fun VoidEq (H >> P) =
    let (* val #[void, void', univ] = P ^! EQ
        val #[] = void ^! VOID
        val #[] = void' ^! VOID
        val (UNIV _, #[]) = asApp univ*)
    in ID
    end*)
  end

  (*val VoidElim : tactic = FAIL*)
  val VoidEq : tactic = FAIL

  fun Elim {target, names, term} world =
    let
      val twoNames = take2 names
      val fourNames = take4 names
    in
      (VoidElim world THEN Hypothesis target)
        (*ORELSE UnitElim target*)
        ORELSE_LAZY (fn _ => BaseElimEq (target, listAt (names, 0)))
        ORELSE_LAZY (fn _ => PlusElim (target, twoNames))
        ORELSE_LAZY (fn _ => ProdElim (target, twoNames))
        ORELSE_LAZY (fn _ => FunElim (target, valOf term, twoNames))
        ORELSE_LAZY (fn _ => IsectElim (target, valOf term, twoNames))
        ORELSE ImageEqInd (target, fourNames)
        ORELSE ImageElim (target, listAt (names, 0))
        ORELSE NatElim (target, twoNames)
        ORELSE SubsetElim (target, twoNames)
    end

  fun EqCD {names, level, invertible, terms} =
    let
      val freshVariable = listAt (names, 0)
    in
        EqEq
        ORELSE EqMemEq
        ORELSE CEqEq
        ORELSE CEqMemEq
        ORELSE ApproxEq
        ORELSE ApproxMemEq
        ORELSE VoidEq
        ORELSE HypEq
        ORELSE UnivEq
        ORELSE PlusEq
        ORELSE InlEq level
        ORELSE InrEq level
        ORELSE BaseEq
        ORELSE BaseMemberEq
        ORELSE FunEq freshVariable
        ORELSE IsectEq freshVariable
        ORELSE ProdEq freshVariable
        ORELSE SubsetEq freshVariable
        ORELSE PairEq (freshVariable, level)
        ORELSE LamEq (freshVariable, level)
        ORELSE SubsetMemberEq (freshVariable, level)
        ORELSE IsectMemberEq (freshVariable, level)
        ORELSE_LAZY (fn _ =>
          case terms of
               [M, N] => IsectMemberCaseEq (SOME M, N)
             | [N] => IsectMemberCaseEq (NONE, N)
             | _ => FAIL)
        ORELSE NatEq
        ORELSE ZeroEq
        ORELSE SuccEq
        ORELSE Cum level
        ORELSE EqInSupertype
        ORELSE ImageEq
        ORELSE ImageMemEq
        ORELSE
        (if not invertible then
             NatRecEq (listAt (terms, 0), take2 names)
               ORELSE_LAZY (fn _ => DecideEq (List.nth (terms, 0))
                                             (List.nth (terms, 1),
                                              List.nth (terms, 2),
                                              take3 names))
               ORELSE SpreadEq (listAt (terms, 0), listAt (terms, 1), take3 names)
               ORELSE ApEq (listAt (terms, 0))
         else
             FAIL)

    end

  fun Ext {freshVariable, level} =
    FunExt (freshVariable, level)
    ORELSE ApproxExtEq

  fun Match [] = FAIL
    | Match [{hyps, goal, branch}] = MatchSingle (hyps, goal, branch)
    | Match ({hyps, goal, branch} :: branches) =
      MatchSingle (hyps, goal, branch)
      ORELSE_LAZY (fn () => Match branches)

  local
    val InvAutoEqCD = EqCD {names = [],
                            level = NONE,
                            invertible = true,
                            terms = []}
    val AutoEqCD = EqCD {names = [],
                         level = NONE,
                         invertible = false,
                         terms = []}

    fun AutoVoidElim world = VoidElim world THEN Assumption

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

    val DeepReduce = RewriteGoal (CDEEP Step)
  in
    fun FinAuto (wld, 0) = LIMIT (UnfoldHead wld ORELSE InvAutoIntro ORELSE AutoVoidElim wld ORELSE InvAutoEqCD)
      | FinAuto (wld, n) = FinAuto (wld, 0) THEN (AutoIntro ORELSE AutoEqCD) THEN FinAuto (wld, n - 1)

    fun InfAuto wld = LIMIT (UnfoldHead wld ORELSE AutoIntro ORELSE AutoVoidElim wld ORELSE AutoEqCD)

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
  (structure Syntax = Syntax and Lcf = Lcf and Conv = Conv and Refiner = Refiner)
