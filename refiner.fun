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
    val Cum : Syn.t -> tactic
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
    val SpreadEq : Syn.t -> Syn.t -> Sequent.name * Sequent.name * Sequent.name -> tactic

    val FunEq : Sequent.name -> tactic
    val FunIntro : Sequent.name -> Syn.t -> tactic
    val FunElim : Sequent.name -> Syn.t -> Sequent.name * Sequent.name -> tactic
    val LamEq : Sequent.name -> Syn.t -> tactic
    val ApEq : Syn.t -> tactic

    val MemUnfold : tactic
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

  fun ctx_subst (H : context) (m : Syn.t) (x : Context.name) =
    Context.map (Syn.subst m x) H

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

    fun @@ (H, (x,A)) = Context.insert H x A
    infix 8 @@

    fun ^! (M, O) =
      case out M of
           O' $ ES => if Operator.eq O O' then ES else raise Refine
         | _ => raise Refine
    infix ^!

    fun as_variable M =
      case out M of
           ` x => x
         | _ => raise Refine

    fun assert_level_lt (l, k) =
      let
        val #[k'] = k ^! LSUCC
      in
        if Syn.eq (l, k') then () else assert_level_lt (l, k')
      end

    fun unify M N =
      if Syn.eq (M, N) then M else raise Refine


    fun Cum k : tactic =
      named "Cum" (fn (H >> P) =>
        let
          val #[A, B, univ] = P ^! EQ
          val #[l] = univ ^! UNIV
          val _ = assert_level_lt (k, l)
        in
          [H >> EQ $$ #[A,B, UNIV $$ #[k]]] BY mk_evidence CUM
        end)

    val UnivEq : tactic =
      named "UnivEq" (fn (H >> P) =>
        let
          val #[univ1, univ2, univ3] = P ^! EQ
          val #[l] = univ1 ^! UNIV
          val #[l'] = univ2 ^! UNIV
          val #[k] = univ3 ^! UNIV
          val l'' = unify l l'
          val _ = assert_level_lt (l'', k)
        in
          [] BY mk_evidence UNIV_EQ
        end)

    val UnitIntro : tactic =
      named "UnitIntro" (fn (H >> P) =>
        let
          val #[] = P ^! UNIT
        in
          [] BY mk_evidence UNIT_INTRO
        end)

    fun UnitElim x : tactic =
      named "UnitElim" (fn (H >> P) =>
        let
          val #[] = Context.lookup H x ^! UNIT
          val ax = AX $$ #[]
          val H' = ctx_subst H ax x
          val P' = subst ax x P
        in
          [ H' >> P'
          ] BY (fn [D] => UNIT_ELIM $$ #[`` x, D]
                 | _ => raise Refine)
        end)

    val UnitEq : tactic =
      named "UnitEq" (fn (H >> P) =>
        let
          val #[unit, unit', univ] = P ^! EQ
          val #[] = unit ^! UNIT
          val #[] = unit' ^! UNIT
          val #[_] = univ ^! UNIV
        in
          [] BY mk_evidence UNIT_EQ
        end)

    val VoidEq : tactic =
      named "VoidEq" (fn (H >> P) =>
        let
          val #[void, void', univ] = P ^! EQ
          val #[] = void ^! VOID
          val #[] = void' ^! VOID
          val #[_] = univ ^! UNIV
        in
          [] BY mk_evidence VOID_EQ
        end)

    val VoidElim : tactic =
      named "VoidEq" (fn (H >> P) =>
        [ H >> VOID $$ #[]
        ] BY mk_evidence VOID_ELIM)

    val AxEq : tactic =
      named "AxEq" (fn (H >> P) =>
        let
          val #[ax, ax', unit] = P ^! EQ
          val #[] = ax ^! AX
          val #[] = ax' ^! AX
          val #[] = unit ^! UNIT
        in
          [] BY mk_evidence AX_EQ
        end)

    fun FunEq z : tactic =
      named "FunEq" (fn (H >> P) =>
        let
          val #[fun1, fun2, univ] = P ^! EQ
          val #[A, xB] = fun1 ^! FUN
          val #[A', yB'] = fun2 ^! FUN
          val #[k] = univ ^! UNIV
        in
          [ H >> EQ $$ #[A,A',univ]
          , H @@ (z,A) >> EQ $$ #[xB // ``z, yB' // `` z, univ]
          ] BY (fn [D, E] => FUN_EQ $$ #[D, z \\ E]
                 | _ => raise Refine)
        end)

    fun FunIntro z k : tactic =
      named "FunIntro" (fn (H >> P) =>
        let
          val #[P1, xP2] = P ^! FUN
        in
          [ H @@ (z,P1) >> xP2 // `` z
          , H >> MEM $$ #[P1, UNIV $$ #[k]]
          ] BY (fn [D,E] => FUN_INTRO $$ #[z \\ D, E]
                 | _ => raise Refine)
        end)

    fun FunElim f s (y, z) : tactic =
      named "FunElim" (fn (H >> P) =>
        let
          val #[S, xT] = Context.lookup H f ^! FUN
          val Ts = xT // s
          val fsTs = EQ $$ #[``y, AP $$ #[``f, s], Ts]
        in
          [ H >> MEM $$ #[s, S]
          , H @@ (y, Ts) @@ (z, fsTs) >> P
          ] BY (fn [D, E] => FUN_ELIM $$ #[``f, s, D, y \\ (z \\ E)]
                  | _ => raise Refine)
        end)

    fun LamEq z k : tactic =
      named "LamEq" (fn (H >> P) =>
        let
          val #[lam, lam', func] = P ^! EQ
          val #[aE] = lam ^! LAM
          val #[bE'] = lam' ^! LAM
          val #[A, cB] = func ^! FUN
        in
          [ H @@ (z,A) >> EQ $$ #[aE // ``z, bE' // ``z, cB // ``z]
          , H >> MEM $$ #[A, UNIV $$ #[k]]
          ] BY (fn [D, E] => LAM_EQ $$ #[z \\ D, E]
                  | _ => raise Refine)
        end)

    fun ApEq funty : tactic =
      named "ApEq" (fn (H >> P) =>
        let
          val #[f1t1, f2t2, Tt1] = P ^! EQ
          val #[f1, t1] = f1t1 ^! AP
          val #[f2, t2] = f2t2 ^! AP
          val #[S, xT] = funty ^! FUN
          val Tt1' = unify Tt1 (xT // t1)
        in
          [ H >> EQ $$ #[f1, f2, funty]
          , H >> EQ $$ #[t1, t2, S]
          ] BY mk_evidence AP_EQ
        end)

    val MemUnfold : tactic =
      named "MemUnfold" (fn (H >> P) =>
        let
          val #[M, A] = P ^! MEM
        in
          [ H >> EQ $$ #[M, M, A]
          ] BY (fn [D] => D
                 | _ => raise Refine)
        end)

    fun Witness M : tactic =
      named "Witness" (fn (H >> P) =>
        [ H >> MEM $$ #[M, P]
        ] BY (fn [D] => WITNESS $$ #[M, D]
               | _ => raise Refine))

    val HypEq : tactic =
      named "HypEq" (fn (H >> P) =>
        let
          val #[M, M', A] = P ^! EQ
          val x = as_variable (unify M M')
          val _ = unify A (Context.lookup H x)
        in
          [] BY (fn _ => HYP_EQ $$ #[`` x])
        end)

    fun ProdEq z : tactic =
      named "ProdEq" (fn (H >> P) =>
        let
          val #[prod1, prod2, univ] = P ^! EQ
          val #[A, xB] = prod1 ^! PROD
          val #[A', yB'] = prod2 ^! PROD
          val #[k] = univ ^! UNIV
        in
          [ H >> EQ $$ #[A,A',univ]
          , H @@ (z,A) >> EQ $$ #[xB // ``z, yB' // ``z, univ]
          ] BY (fn [D, E] => PROD_EQ $$ #[D, z \\ E]
                 | _ => raise Refine)
        end)

    fun ProdIntro w : tactic =
      named "ProdIntro" (fn (H >> P) =>
        let
          val #[P1, xP2] = P ^! PROD
        in
          [ H >> MEM $$ #[ w, P1]
          , H >> xP2 // w
          ] BY (fn [D, E] => PROD_INTRO $$ #[w, D, E]
                 | _ => raise Refine)
        end)

    fun ProdElim z (s, t) : tactic =
      named "ProdElim" (fn (H >> P) =>
        let
          val #[S, xT] = Context.lookup H z ^! PROD
          val st = PAIR $$ #[``s, ``t]
          val H' = ctx_subst H st z @@ (s, S) @@ (t, (xT // `` s))
        in
          [ H' >> subst st z P
          ] BY (fn [D] => PROD_ELIM $$ #[``z, s \\ (t \\ D)]
                 | _ => raise Refine)
        end)

    fun PairEq z k : tactic =
      named "PairEq" (fn (H >> P) =>
        let
          val #[pair, pair', prod] = P ^! EQ
          val #[M, N] = pair ^! PAIR
          val #[M', N'] = pair' ^! PAIR
          val #[A, xB] = prod ^! PROD
        in
          [ H >> EQ $$ #[M, M', A]
          , H >> EQ $$ #[N, N', xB // M]
          , H @@ (z,A) >> MEM $$ #[xB // `` z, UNIV $$ #[k]]
          ] BY (fn [D,E,F] => PAIR_EQ $$ #[D, E, z \\ F]
                 | _ => raise Refine)
        end)

    fun SpreadEq zC prod (s, t, y) : tactic =
      named "SpreadEq" (fn (H >> P) =>
        let
          val #[spread, spread', CE1] = P ^! EQ
          val #[S, xT] = prod ^! PROD
          val #[E1, xyT1] = spread ^! SPREAD
          val #[E2, uvT2] = spread' ^! SPREAD
          val CE1' = unify CE1 (zC // E1)
          val Ts = xT // ``s
          val st = PAIR $$ #[``s, ``t]
          val E1pair = EQ $$ #[E1, st, prod]
          val Cst = zC // st
          val T1st = (xyT1 // ``s) // ``t
          val T2st = (uvT2 // ``s) // ``t
          exception XXX
        in
          [ H >> EQ $$ #[E1, E2, prod]
          , H @@ (s, S) @@ (t, Ts) @@ (y, E1pair) >> EQ $$ #[T1st, T2st, Cst]
          ] BY (fn [D, E] => SPREAD_EQ $$ #[D, s \\ (t \\ (y \\ E))]
                  | _ => raise Refine)
        end)

    fun Hypothesis x : tactic =
      named "Hypothesis" (fn (H >> P) =>
        if Syn.eq (P, Context.lookup H x)
        then [] BY (fn _ => `` x)
        else raise Refine)

    val Assumption : tactic =
      named "Assumption" (fn (H >> P) =>
        case Context.search H (fn x => Syn.eq (P, x)) of
             SOME (x, _) => [] BY (fn _ => `` x)
           | NONE => raise Refine)

    fun Lemma lem : tactic =
      named "Lemma" (fn (H >> P) =>
        let
          val (H' >> P') = Library.goal lem
        in
          if Context.subcontext Syn.eq (H', H) andalso Syn.eq (P, P')
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
      val EqAuto = CanEqAuto ORELSE HypEq
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

