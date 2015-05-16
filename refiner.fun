functor Refiner
  (structure Syn : ABT_UTIL where Operator = Operator
   structure Sequent : SEQUENT
     where type term = Syn.t
     and type name = Syn.Variable.t
   val print_mode : PrintMode.t) :>
sig
  type evidence = Syn.t
  type validation = evidence list -> evidence
  type tactic = Sequent.sequent -> Sequent.sequent list * validation

  structure Library : LIBRARY
    where type goal = Sequent.sequent
      and type evidence = evidence
      and type tactic = tactic

  structure CoreTactics : CORE_TACTICS
    where type tactic = tactic

  structure InferenceRules :
  sig
    val UnivEq : tactic
    val VoidEq : tactic
    val VoidElim : tactic

    val UnitEq : tactic
    val UnitIntro : tactic
    val UnitElim : Sequent.name -> tactic
    val AxEq : tactic

    val ProdEq : Sequent.name -> tactic
    val ProdIntro : Syn.t -> tactic
    val ProdElim : Sequent.name -> Sequent.name * Sequent.name -> tactic
    val PairEq : Sequent.name -> Syn.t -> tactic

    val FunEq : Sequent.name -> tactic
    val FunIntro : Sequent.name -> Syn.t -> tactic
    val LamEq : Sequent.name -> Syn.t -> tactic

    val MemUnfold : tactic
    val ReduceGoal : tactic
    val Witness : Syn.t -> tactic

    val Assumption : tactic
    val Hypothesis : Sequent.name -> tactic
    val HypEq : tactic
    val Lemma : Library.t -> tactic
  end

  structure DerivedTactics :
  sig
    val Auto : tactic
  end
end =
struct
  structure Context = Sequent.Context
  type context = Sequent.context

  fun ctx_subst (G : context) (m : Syn.t) (x : Context.name) =
    Context.map (Syn.subst m x) G

  structure RefinerTypes =
    RefinerTypes
      (structure Sequent = Sequent
       type evidence = Syn.t)

  open RefinerTypes

  open Operator Syn
  infix $ \
  infix 8 $$ // \\

  structure Whnf = Whnf(Syn)

  structure CoreTactics = CoreTactics(RefinerTypes)
  structure Library = Library(RefinerTypes)

  structure InferenceRules =
  struct
    exception Refine
    open Sequent
    infix >>

    fun named name (tac : tactic) : tactic = fn (goal : goal) =>
      let
        fun fail () = raise Fail (name ^ "| " ^ goal_to_string goal)
        val (subgoals, validation) = tac goal handle _ => fail ()
      in
        (subgoals, fn Ds => validation Ds handle _ => fail ())
      end

    fun mk_evidence operator = fn Ds => operator $$ Vector.fromList Ds

    fun BY (Ds, V) = (Ds, V)
    infix BY

    fun @@ (G, (x,A)) = Context.insert G x A
    infix 8 @@

    fun assert_level_lt (l, k) =
      case out k of
           LSUCC $ #[k'] => if Syn.eq (l, k') then () else assert_level_lt (l, k')
         | _ => raise Refine

    val UnivEq : tactic =
      named "UnivEq" (fn (G >> P) =>
        case out P of
             EQ $ #[univ1, univ2, univ3] =>
             (case (out univ1, out univ2, out univ3) of
                   (UNIV $ #[l], UNIV $ #[l'], UNIV $ #[k]) =>
                   if Syn.eq (l, l')
                   then (assert_level_lt (l, k); [] BY mk_evidence UNIV_EQ)
                   else raise Refine
                 | _ => raise Refine)
           | _ => raise Refine)

    val UnitIntro : tactic =
      named "UnitIntro" (fn (G >> P) =>
        case out P of
             UNIT $ _ => [] BY mk_evidence UNIT_INTRO
           | _ => raise Refine)

    fun UnitElim x : tactic =
      named "UnitElim" (fn (G >> P) =>
        case out (Context.lookup G x) of
             UNIT $ #[] =>
               let
                 val ax = AX $$ #[]
                 val G' = ctx_subst G ax x
                 val P' = subst ax x P
               in
                 [ G' >> P'
                 ] BY (fn [D] => UNIT_ELIM $$ #[`` x, D]
                        | _ => raise Refine)
               end
           | _ => raise Refine)

    val UnitEq : tactic =
      named "UnitEq" (fn (G >> P) =>
        case out P of
             EQ $ #[unit, unit', univ] =>
               (case (out unit, out unit', out univ) of
                    (UNIT $ _, UNIT $ _, UNIV $ _) =>
                      [] BY mk_evidence UNIT_EQ
                  | _ => raise Refine)
           | _ => raise Refine)

    val VoidEq : tactic =
      named "VoidEq" (fn (G >> P) =>
        case out P of
             EQ $ #[void, void', univ] =>
               (case (out void, out void', out univ) of
                    (VOID $ _, VOID $ _, UNIV $ _) =>
                      [] BY mk_evidence VOID_EQ
                  | _ => raise Refine)
           | _ => raise Refine)

    val VoidElim : tactic =
      named "VoidEq" (fn (G >> P) =>
        [ G >> VOID $$ #[]
        ] BY mk_evidence VOID_ELIM)

    val AxEq : tactic =
      named "AxEq" (fn (G >> P) =>
        case out P of
             EQ $ #[ax, ax', unit] =>
               (case (out ax, out ax', out unit) of
                    (AX $ #[], AX $ #[], UNIT $ #[]) =>
                      [] BY mk_evidence AX_EQ
                  | _ => raise Refine)
           | _ => raise Refine)

    fun FunEq z : tactic =
      named "FunEq" (fn (G >> P) =>
        case out P of
             EQ $ #[fun1, fun2, univ] =>
               (case (out fun1, out fun1, out univ) of
                    (FUN $ #[A,xB], FUN $ #[A',yB'], UNIV $ #[k]) =>
                      [ G >> EQ $$ #[A,A',univ]
                      , G @@ (z,A) >> EQ $$ #[xB // ``z, yB' // `` z, univ]
                      ] BY (fn [D, E] => FUN_EQ $$ #[D, z \\ E]
                             | _ => raise Refine)
                  | _ => raise Refine)
           | _ => raise Refine)

    fun FunIntro z k : tactic =
      named "FunIntro" (fn (G >> P) =>
        case out P of
             FUN $ #[P1, xP2] =>
               [ G @@ (z,P1) >> xP2 // `` z
               , G >> MEM $$ #[P1, UNIV $$ #[k]]
               ] BY (fn [D,E] => FUN_INTRO $$ #[z \\ D, E]
                      | _ => raise Refine)
           | _ => raise Refine)

    fun LamEq z k : tactic =
      named "LamEq" (fn (G >> P) =>
        case out P of
             EQ $ #[lam, lam', func] =>
               (case (out lam, out lam', out func) of
                     (LAM $ #[aE], LAM $ #[bE'], FUN $ #[A,cB]) =>
                       [ G @@ (z,A) >> EQ $$ #[aE // ``z, bE' // ``z, cB // ``z]
                       , G >> MEM $$ #[A, UNIV $$ #[k]]
                       ] BY (fn [D, E] => LAM_EQ $$ #[z \\ D, E]
                               | _ => raise Refine)
                   | _ => raise Refine)
           | _ => raise Refine)

    val MemUnfold : tactic =
      named "MemUnfold" (fn (G >> P) =>
      case out P of
           MEM $ #[M, A] =>
             [ G >> EQ $$ #[M, M, A]
             ] BY (fn [D] => D
                    | _ => raise Refine)
         | _ => raise Refine)

    val ReduceGoal : tactic =
      named "ReduceGoal" (fn (G >> P) =>
        case out P of
             EQ $ #[M, N, A] =>
               let
                 val M0 = Whnf.whnf M handle _ => M
                 val N0 = Whnf.whnf N handle _ => N
                 val A0 = Whnf.whnf A handle _ => A
               in
                 [ G >> EQ $$ #[M0, N0, A0]
                 ] BY (fn [D] => D
                        | _ => raise Refine)
               end
           | _ => raise Refine)

    fun Witness M : tactic =
      named "Witness" (fn (G >> P) =>
        [ G >> MEM $$ #[M, P]
        ] BY (fn [D] => WITNESS $$ #[M, D]
               | _ => raise Refine))

    val HypEq : tactic =
      named "HypEq" (fn (G >> P) =>
        case out P of
             EQ $ #[M,M',A] =>
             (case (Syn.eq (M, M'), out M) of
                   (true, ` x) =>
                      if Syn.eq (A, Context.lookup G x)
                      then [] BY (fn _ => HYP_EQ $$ #[`` x])
                      else raise Refine
                 | _ => raise Refine)
           | _ => raise Refine)

    fun ProdEq z : tactic =
      named "ProdEq" (fn (G >> P) =>
        case out P of
             CAN_EQ $ #[prod1, prod2, univ] =>
               (case (out prod1, out prod2, out univ) of
                    (PROD $ #[A,xB], PROD $ #[A',yB'], UNIV $ #[k]) =>
                      [ G >> EQ $$ #[A,A',univ]
                      , G @@ (z,A) >> EQ $$ #[xB // ``z, yB' // ``z, univ]
                      ] BY (fn [D, E] => PROD_EQ $$ #[D, z \\ E]
                             | _ => raise Refine)
                  | _ => raise Refine)
           | _ => raise Refine)

    fun ProdIntro w : tactic =
      named "ProdIntro" (fn (G >> P) =>
        case out P of
             PROD $ #[P1, xP2] =>
               [ G >> MEM $$ #[ w, P1]
               , G >> xP2 // w
               ] BY (fn [D, E] => PROD_INTRO $$ #[w, D, E]
                      | _ => raise Refine)
           | _ => raise Refine)

    fun ProdElim z (s, t) : tactic =
      named "ProdElim" (fn (G >> P) =>
        case out (Context.lookup G z) of
             PROD $ #[ S, xT ] =>
               let
                 val st = PAIR $$ #[``s, ``t]
                 val G' = ctx_subst G st z @@ (s, S) @@ (t, (xT // `` s))
               in
                 [ G' >> subst st z P
                 ] BY (fn [D] => PROD_ELIM $$ #[``z, s \\ (t \\ D)]
                        | _ => raise Refine)
               end
           | _ => raise Refine)

    fun PairEq z k : tactic =
      named "PairEq" (fn (G >> P) =>
        case out P of
             CAN_EQ $ #[pair, pair', prod] =>
               (case (out pair, out pair', out prod) of
                     (PAIR $ #[M,N], PAIR $ #[M', N'], PROD $ #[A,xB]) =>
                       [ G >> EQ $$ #[M, M', A]
                       , G >> EQ $$ #[N, N', xB // M]
                       , G @@ (z,A) >> MEM $$ #[xB // `` z, UNIV $$ #[k]]
                       ] BY (fn [D,E,F] => PAIR_EQ $$ #[D, E, z \\ F]
                              | _ => raise Refine)
                   | _ => raise Refine)
           | _ => raise Refine)

    fun Hypothesis x : tactic =
      named "Hypothesis" (fn (G >> P) =>
        if Syn.eq (P, Context.lookup G x)
        then [] BY (fn _ => `` x)
        else raise Refine)

    val Assumption : tactic =
      named "Assumption" (fn (G >> P) =>
        case Context.search G (fn x => Syn.eq (P, x)) of
             SOME (x, _) => [] BY (fn _ => `` x)
           | NONE => raise Refine)

    fun Lemma lem : tactic =
      named "Lemma" (fn (G >> P) =>
        let
          val (G' >> P') = Library.goal lem
        in
          if Context.subcontext Syn.eq (G', G) andalso Syn.eq (P, P')
          then [] BY (fn _ => Library.validate lem)
          else raise Refine
        end)
  end

  structure DerivedTactics =
  struct
    open CoreTactics InferenceRules
    infix ORELSE ORELSE_LAZY THEN

    local
      val i = Variable.named "i"
      val CanEqAuto = AxEq ORELSE_LAZY (fn () => PairEq (Variable.new ()) (`` i)) ORELSE_LAZY (fn () => LamEq (Variable.new ()) (`` i)) ORELSE UnitEq ORELSE_LAZY (fn () => ProdEq (Variable.new())) ORELSE VoidEq ORELSE UnivEq
      val EqAuto = (ReduceGoal THEN CanEqAuto) ORELSE HypEq
      val intro_rules =
        MemUnfold ORELSE
          EqAuto ORELSE
            Assumption ORELSE_LAZY
              (fn () => FunIntro (Variable.new ()) (`` i)) ORELSE
                UnitIntro
    in
      val Auto = REPEAT0 intro_rules
    end
  end
end

