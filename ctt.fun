functor Ctt
  (structure Syntax : ABT_UTIL
     where Operator = Operator
   structure Context : CONTEXT
     where type name = Syntax.Variable.t
   structure Sequent : SEQUENT
     where type name = Context.name
     where type context = Syntax.t Context.context
     where type term = Syntax.t
   structure Lcf : LCF
     where type goal = Sequent.sequent
     where type evidence = Syntax.t
   structure ConvTypes : CONV_TYPES
     where Syntax = Syntax
   structure Development : DEVELOPMENT
     where Lcf = Lcf
     where type label = string
     where type term = Syntax.t) : CTT =
struct
  type tactic = Lcf.tactic
  type conv = ConvTypes.conv
  type name = Sequent.name
  type term = Syntax.t
  type goal = Sequent.sequent

  structure Development = Development
  structure Conversionals = Conversionals
    (structure Syntax = Syntax
     structure ConvTypes = ConvTypes)

  open Operator Syntax
  infix $ \
  infix 8 $$ // \\

  structure Rules =
  struct
    exception Refine
    open Sequent
    infix >>

    fun ctx_subst (H : context) (m : Syntax.t) (x : Context.name) =
      Context.map_after x (Syntax.subst m x) H

    fun ctx_unbind (H : context, A : Syntax.t, xE : Syntax.t) =
      let
        val (x, E) = unbind xE
        val x' = Context.fresh (H, x)
        val H' = Context.insert H x' Visibility.Visible A
        val E' = subst (``x') x E
      in
        (H', x', E')
      end

    fun named name (tac : tactic) : tactic = fn (goal : goal) =>
      let
        fun fail () = raise Fail (name ^ "| " ^ Lcf.goal_to_string goal)
        val (subgoals, validation) = tac goal handle Refine => fail ()
      in
        (subgoals, fn Ds => validation Ds handle Refine => fail ())
      end

    fun mk_evidence operator = fn Ds => operator $$ Vector.fromList Ds

    fun BY (Ds, V) = (Ds, V)
    infix BY

    fun @@ (H, (x,A)) = Context.insert H x Visibility.Visible A
    infix 8 @@

    fun as_app M =
      case out M of
           O $ ES => (O, ES)
         | _ => raise Refine

    fun ^! (M, O) =
      case out M of
           O' $ ES => if Operator.eq (O, O') then ES else raise Refine
         | _ => raise Refine
    infix ^!

    fun as_variable M =
      case out M of
           ` x => x
         | _ => raise Refine

    fun unify M N =
      if Syntax.eq (M, N) then M else raise Refine

    fun operator_irrelevant O =
      case O of
           EQ => true
         | MEM => true
         | SQUASH => true
         | UNIT => true
         | _ => false

    fun assert_irrelevant (H, P) =
      case out P of
           O $ _ => if operator_irrelevant O then () else raise Refine
         | _ => raise Refine

    fun infer_level (H, P) =
      case out P of
           UNIV l $ _ => l + 1
         | FUN $ #[A, xB] =>
           let
             val (H', x, B) = ctx_unbind (H, A, xB)
           in
             Level.max (infer_level (H, A), infer_level (H', B))
           end
         | PROD $ #[A, xB] =>
           let
             val (H', x, B) = ctx_unbind (H, A, xB)
           in
             Level.max (infer_level (H, A), infer_level (H', B))
           end
         | ISECT $ #[A, xB] =>
           let
             val (H', x, B) = ctx_unbind (H, A, xB)
           in
             Level.max (infer_level (H, A), infer_level (H', B))
           end

         | SQUASH $ #[A] => infer_level (H, A)
         | ` x =>
            let
              val X = Context.lookup H x
              val k = infer_level (H, X)
            in
              k - 1
            end
         | _ => 0

    fun infer_type (H, M) =
      case out M of
           UNIV l $ _ => UNIV (l + 1) $$ #[]
         | SQUASH $ #[A] => infer_type (H, A)
         | AP $ #[F, N] =>
             let
               val #[A, xB] = infer_type (H, F) ^! FUN
             in
               xB // N
             end
         | SPREAD $ #[X, uvE] =>
             let
               val #[A, xB] = infer_type (H, X) ^! PROD
               val (H', u, vE) = ctx_unbind (H, A, uvE)
               val (H'', v, E) = ctx_unbind (H', xB // ``u, vE)
             in
               infer_type (H'', E)
             end
         | ` x => Context.lookup H x
         | _ => raise Refine

    fun Cum ok : tactic =
      named "Cum" (fn (H >> P) =>
        let
          val #[A, B, univ] = P ^! EQ
          val (UNIV l, #[]) = as_app univ
          val k = case ok of NONE => Level.max (infer_level (H, A), infer_level (H, B)) | SOME k => k
          val _ = Level.assert_lt (k, l)
        in
          [H >> EQ $$ #[A,B, UNIV k $$ #[]]] BY mk_evidence CUM
        end)

    val UnivEq : tactic =
      named "UnivEq" (fn (H >> P) =>
        let
          val #[univ1, univ2, univ3] = P ^! EQ
          val (UNIV l, #[]) = as_app univ1
          val (UNIV l', #[]) = as_app univ2
          val (UNIV k, #[]) = as_app univ3
          val _ = Level.assert_lt (Level.unify (l, l'), k)
        in
          [] BY mk_evidence UNIV_EQ
        end)

    val EqEq : tactic =
      named "EqEq" (fn (H >> P) =>
        let
          val #[E1, E2, univ] = P ^! EQ
          val (UNIV k, #[]) = as_app univ
          val #[M,N,A] = E1 ^! EQ
          val #[M',N',A'] = E2 ^! EQ
        in
          [ H >> EQ $$ #[A,A',univ]
          , H >> EQ $$ #[M,M',A]
          , H >> EQ $$ #[N,N',A]
          ] BY mk_evidence EQ_EQ
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
          val (UNIV _, #[]) = as_app univ
        in
          [] BY mk_evidence UNIT_EQ
        end)

    val VoidEq : tactic =
      named "VoidEq" (fn (H >> P) =>
        let
          val #[void, void', univ] = P ^! EQ
          val #[] = void ^! VOID
          val #[] = void' ^! VOID
          val (UNIV _, #[]) = as_app univ
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

    val SquashEq : tactic =
      named "SquashEq" (fn (H >> P) =>
        let
          val #[sq1, sq2, univ] = P ^! EQ
          val #[P1] = sq1 ^! SQUASH
          val #[P2] = sq2 ^! SQUASH
          val (UNIV _, #[]) = as_app univ
        in
          [ H >> EQ $$ #[P1, P2, univ]
          ] BY mk_evidence SQUASH_EQ
        end)

    val SquashIntro : tactic =
      named "SquashIntro" (fn (H >> P) =>
        let
          val #[P'] = P ^! SQUASH
        in
          [ H >> P'
          ] BY mk_evidence SQUASH_INTRO
        end)

    fun SquashElim z : tactic =
      named "SquashElim" (fn (H >> P) =>
        let
          val #[M, N, A] = P ^! EQ

          fun unsquash Z =
            let val #[Z'] = Z ^! SQUASH in Z' end

          val ax = AX $$ #[]
          val H' = ctx_subst (Context.modify H z unsquash) ax z
        in
          [ H' >> subst ax z P
          ] BY mk_evidence SQUASH_ELIM
        end)

    fun FunEq oz : tactic =
      named "FunEq" (fn (H >> P) =>
        let
          val #[fun1, fun2, univ] = P ^! EQ
          val #[A, xB] = fun1 ^! FUN
          val #[A', yB'] = fun2 ^! FUN
          val (UNIV _, #[]) = as_app univ

          val z =
            Context.fresh (H,
              case oz of
                   NONE => #1 (unbind xB)
                 | SOME z => z)
        in
          [ H >> EQ $$ #[A,A',univ]
          , H @@ (z,A) >> EQ $$ #[xB // ``z, yB' // `` z, univ]
          ] BY (fn [D, E] => FUN_EQ $$ #[D, z \\ E]
                 | _ => raise Refine)
        end)

    fun FunIntro oz ok : tactic =
      named "FunIntro" (fn (H >> P) =>
        let
          val #[P1, xP2] = P ^! FUN
          val z =
            Context.fresh (H,
              case oz of
                   NONE => #1 (unbind xP2)
                 | SOME z => z)
          val k = case ok of NONE => infer_level (H, P1) | SOME k => k
        in
          [ H @@ (z,P1) >> xP2 // `` z
          , H >> MEM $$ #[P1, UNIV k $$ #[]]
          ] BY (fn [D,E] => FUN_INTRO $$ #[z \\ D, E]
                 | _ => raise Refine)
        end)

    fun FunElim f s onames : tactic =
      named "FunElim" (fn (H >> P) =>
        let
          val #[S, xT] = Context.lookup H f ^! FUN
          val Ts = xT // s
          val (y, z) =
            case onames of
                 SOME names => names
               | NONE =>
                   (Context.fresh (H, Variable.named "y"),
                    Context.fresh (H, Variable.named "z"))

          val fsTs = EQ $$ #[``y, AP $$ #[``f, s], Ts]
        in
          [ H >> MEM $$ #[s, S]
          , H @@ (y, Ts) @@ (z, fsTs) >> P
          ] BY (fn [D, E] => FUN_ELIM $$ #[``f, s, D, y \\ (z \\ E)]
                  | _ => raise Refine)
        end)

    fun LamEq oz ok : tactic =
      named "LamEq" (fn (H >> P) =>
        let
          val #[lam, lam', func] = P ^! EQ
          val #[aE] = lam ^! LAM
          val #[bE'] = lam' ^! LAM
          val #[A, cB] = func ^! FUN
          val z =
            Context.fresh (H,
              case oz of
                   NONE => #1 (unbind cB)
                 | SOME z => z)
          val k = case ok of NONE => infer_level (H, A) | SOME k => k
        in
          [ H @@ (z,A) >> EQ $$ #[aE // ``z, bE' // ``z, cB // ``z]
          , H >> MEM $$ #[A, UNIV k $$ #[]]
          ] BY (fn [D, E] => LAM_EQ $$ #[z \\ D, E]
                  | _ => raise Refine)
        end)

    fun ApEq ofunty : tactic =
      named "ApEq" (fn (H >> P) =>
        let
          val #[f1t1, f2t2, Tt1] = P ^! EQ
          val #[f1, t1] = f1t1 ^! AP
          val #[f2, t2] = f2t2 ^! AP
          val funty =
            case ofunty of
                 NONE => unify (infer_type (H, f1)) (infer_type (H, f2))
               | SOME funty => funty
          val #[S, xT] = funty ^! FUN
          val Tt1' = unify Tt1 (xT // t1)
        in
          [ H >> EQ $$ #[f1, f2, funty]
          , H >> EQ $$ #[t1, t2, S]
          ] BY mk_evidence AP_EQ
        end)

    fun IsectEq oz : tactic =
      named "IsectEq" (fn (H >> P) =>
        let
          val #[isect1, isect2, univ] = P ^! EQ
          val #[A, xB] = isect1 ^! ISECT
          val #[A', yB'] = isect2 ^! ISECT
          val (UNIV _, #[]) = as_app univ

          val z =
            Context.fresh (H,
              case oz of
                   NONE => #1 (unbind xB)
                 | SOME z => z)
        in
          [ H >> EQ $$ #[A,A',univ]
          , H @@ (z,A) >> EQ $$ #[xB // ``z, yB' // `` z, univ]
          ] BY (fn [D, E] => ISECT_EQ $$ #[D, z \\ E]
                 | _ => raise Refine)
        end)

    fun IsectIntro oz ok : tactic =
      named "IsectIntro" (fn (H >> P) =>
        let
          val #[P1, xP2] = P ^! ISECT
          val z =
            Context.fresh (H,
              case oz of
                   NONE => #1 (unbind xP2)
                 | SOME z => z)
          val k = case ok of NONE => infer_level (H, P1) | SOME k => k
          val H' = Context.insert H z Visibility.Hidden P1
        in
          [ H' >> xP2 // `` z
          , H >> MEM $$ #[P1, UNIV k $$ #[]]
          ] BY (fn [D,E] => ISECT_INTRO $$ #[z \\ D, E]
                 | _ => raise Refine)
        end)

    fun IsectElim f s onames : tactic =
      named "IsectElim" (fn (H >> P) =>
        let
          val #[S, xT] = Context.lookup H f ^! ISECT
          val Ts = xT // s
          val (y, z) =
            case onames of
                 SOME names => names
               | NONE =>
                   (Context.fresh (H, Variable.named "y"),
                    Context.fresh (H, Variable.named "z"))

          val fsTs = EQ $$ #[``y, ``f, Ts]
        in
          [ H >> MEM $$ #[s, S]
          , H @@ (y, Ts) @@ (z, fsTs) >> P
          ] BY (fn [D, E] => FUN_ELIM $$ #[``f, s, D, y \\ (z \\ E)]
                  | _ => raise Refine)
        end)

    fun IsectMemberEq oz ok : tactic =
      named "IsectMemberEq" (fn (H >> P) =>
        let
          val #[M,N,A] = P ^! EQ
          val #[P1, xP2] = A ^! ISECT
          val z =
            Context.fresh (H,
              case oz of
                   NONE => #1 (unbind xP2)
                 | SOME z => z)
          val k = case ok of NONE => infer_level (H, P1) | SOME k => k
          val H' = Context.insert H z Visibility.Hidden P1
        in
          [ H' >> EQ $$ #[M,N, xP2 // ``z]
          , H >> MEM $$ #[P1, UNIV k $$ #[]]
          ] BY (fn [D, E] => ISECT_MEMBER_EQ $$ #[z \\ D, E]
                 | _ => raise Refine)
        end)

    fun IsectMemberCaseEq oisect t : tactic =
      named "IsectMemberCaseEq" (fn (H >> P) =>
        let
          val #[F1,F2, Tt] = P ^! EQ
          val isect =
            case oisect of
                 SOME isect => isect
               | NONE => unify (infer_type (H, F1)) (infer_type (H, F2))

          val #[S, xT] = isect ^! ISECT
          val _ = unify Tt (xT // t)
        in
          [ H >> EQ $$ #[F1, F2, isect]
          , H >> MEM $$ #[t, S]
          ] BY mk_evidence ISECT_MEMBER_CASE_EQ
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

    fun ProdEq oz : tactic =
      named "ProdEq" (fn (H >> P) =>
        let
          val #[prod1, prod2, univ] = P ^! EQ
          val #[A, xB] = prod1 ^! PROD
          val #[A', yB'] = prod2 ^! PROD
          val (UNIV _, #[]) = as_app univ
          val z =
            Context.fresh (H,
              case oz of
                   NONE => #1 (unbind xB)
                 | SOME z => z)
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

    fun ProdElim z onames : tactic =
      named "ProdElim" (fn (H >> P) =>
        let
          val #[S, xT] = Context.lookup H z ^! PROD
          val (s, t) =
            case onames of
                 SOME names => names
               | NONE =>
                   (Context.fresh (H, Variable.named "s"),
                    Context.fresh (H, Variable.named "t"))

          val st = PAIR $$ #[``s, ``t]
          val J = Context.empty @@ (s, S) @@ (t, (xT // ``s))
          val H' = ctx_subst (Context.interpose_after H (z, J)) st z
        in
          [ H' >> subst st z P
          ] BY (fn [D] => PROD_ELIM $$ #[``z, s \\ (t \\ D)]
                 | _ => raise Refine)
        end)

    fun PairEq oz ok : tactic =
      named "PairEq" (fn (H >> P) =>
        let
          val #[pair, pair', prod] = P ^! EQ
          val #[M, N] = pair ^! PAIR
          val #[M', N'] = pair' ^! PAIR
          val #[A, xB] = prod ^! PROD
          val z =
            Context.fresh (H,
              case oz of
                   NONE => #1 (unbind xB)
                 | SOME z => z)
          val k = case ok of NONE => infer_level (H, A) | SOME k => k
        in
          [ H >> EQ $$ #[M, M', A]
          , H >> EQ $$ #[N, N', xB // M]
          , H @@ (z,A) >> MEM $$ #[xB // `` z, UNIV k $$ #[]]
          ] BY (fn [D,E,F] => PAIR_EQ $$ #[D, E, z \\ F]
                 | _ => raise Refine)
        end)

    fun SpreadEq ozC oprod onames : tactic =
      named "SpreadEq" (fn (H >> P) =>
        let
          val #[spread, spread', CE1] = P ^! EQ
          val #[E1, xyT1] = spread ^! SPREAD
          val #[E2, uvT2] = spread' ^! SPREAD

          val prod =
            case oprod of
                 NONE => unify (infer_type (H, E1)) (infer_type (H, E2))
               | SOME prod => prod

          val (s,t,y) =
            case onames of
                 NONE =>
                  (Context.fresh (H, Variable.named "s"),
                   Context.fresh (H, Variable.named "t"),
                   Context.fresh (H, Variable.named "y"))
               | SOME names => names

          val #[S, xT] = prod ^! PROD

          val zC =
            case ozC of
                 NONE =>
                 let
                   val z = Context.fresh (H, Variable.named "z")
                   val H' = H @@ (z, prod)
                   val Cz =
                     unify
                       (infer_type (H', SPREAD $$ #[``z, xyT1]))
                       (infer_type (H', SPREAD $$ #[``z, uvT2]))
                 in
                   z \\ Cz
                 end
               | SOME zC => zC

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
        let
          val (P', visibility) = Context.lookup_visibility H x
          val P'' = unify P P'
        in
          (case visibility of
               Visibility.Visible => ()
             | Visibility.Hidden => assert_irrelevant (H, P''));
          [] BY (fn _ => ``x)
        end)

    val Assumption : tactic =
      named "Assumption" (fn (H >> P) =>
        case Context.search H (fn x => Syntax.eq (P, x)) of
             SOME (x, _) => Hypothesis x (H >> P)
           | NONE => raise Refine)

    fun Unfold (development, lem) : tactic =
      named "Unfold" (fn (H >> P) =>
        let
          val definiens = Development.lookup_definition development lem
          val rewrite = subst definiens (Variable.named lem)
        in
          [ Context.map rewrite H >> rewrite P
          ] BY (fn [D] => D
                 | _ => raise Refine)
        end)

    fun Lemma (development, lem) : tactic =
      named "Lemma" (fn (H >> P) =>
        let
          val {statement, evidence} = Development.lookup_theorem development lem
          val H' >> P' = statement
        in
          if Context.subcontext Syntax.eq (H', H) andalso Syntax.eq (P, P')
          then [] BY (fn _ => Susp.force evidence)
          else raise Refine
        end)

    val Admit : tactic =
      named "Admit" (fn (H >> P) =>
        [] BY (fn _ => ADMIT $$ #[]))

    fun RewriteGoal (c : conv) : tactic =
      named "RewriteGoal" (fn (H >> P) =>
        [ Context.map c H >> c P ] BY (fn [D] => D | _ => raise Refine))

    val EqSym : tactic =
      named "EqSym" (fn (H >> P) =>
        let
          val #[M,N,A] = P ^! EQ
        in
          [ H >> EQ $$ #[N,M,A]
          ] BY mk_evidence EQ_SYM
        end)

    fun EqSubst eq xC ok : tactic =
      named "EqSubst" (fn (H >> P) =>
        let
          val #[M,N,A] = eq ^! EQ
          val (H', z, C) = ctx_unbind (H, A, xC)
          val P' = unify P (xC // M)
          val k = case ok of SOME k => k | NONE => infer_level (H', C)
        in
          [ H >> eq
          , H >> xC // N
          , H' >> MEM $$ #[C, UNIV k $$ #[]]
          ] BY (fn [D,E,F] => EQ_SUBST $$ #[D, E, z \\ F]
                 | _ => raise Refine)
        end)
  end

  structure Conversions =
  struct
    open Conversionals ConvTypes

    val ApBeta : conv = reduction_rule
      (fn AP $ #[LAM $ #[xE], N] => xE // into N
        | _ => raise Conv)

    val SpreadBeta : conv = reduction_rule
      (fn SPREAD $ #[PAIR $ #[M,N], xyE] => (into xyE // M) // N
        | _ => raise Conv)
  end
end

structure Ctt = Ctt
  (structure Syntax = Syntax
   structure Context = Context
   structure Lcf = Lcf
   structure ConvTypes = ConvTypes
   structure Sequent = Sequent
   structure Development = Development)