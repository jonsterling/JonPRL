functor Ctt
  (structure Lcf : LCF
   structure Development : DEVELOPMENT
     where type judgement = Lcf.goal
     where type evidence = Lcf.evidence
     where type tactic = Lcf.tactic

   structure Syntax : ABT_UTIL
     where type Operator.t = Development.label OperatorType.operator

   structure Sequent : SEQUENT
     where type term = Syntax.t
     where Context.Syntax = Syntax

   sharing type Lcf.goal = Sequent.sequent
   sharing type Lcf.evidence = Syntax.t

   structure Conv : CONV where type term = Syntax.t
   structure Semantics : SMALL_STEP where type syn = Syntax.t
   sharing type Development.term = Syntax.t) : CTT =
struct
  structure Lcf = Lcf
  structure Conv = ConvUtil(structure Conv = Conv and Syntax = Syntax)
  structure Syntax = Syntax

  type tactic = Lcf.tactic
  type conv = Conv.conv
  type name = Sequent.name
  type term = Syntax.t
  type goal = Sequent.sequent
  type world = Development.world
  type label = Development.label

  structure Operator = Syntax.Operator
  structure Development = Development
  structure Conversionals = Conversionals
    (structure Syntax = Syntax
     structure Conv = Conv)

  open Syntax
  open Operator OperatorType
  infix $ \
  infix 8 $$ // \\

  structure Rules =
  struct
    exception Refine
    open Sequent
    infix >>

    fun ctxSubst (H : context) (m : Syntax.t) (x : Context.name) =
      Context.mapAfter x (Syntax.subst m x) H

    fun ctxUnbind (H : context, A : Syntax.t, xE : Syntax.t) =
      let
        val (x, E) = unbind (Context.rebind H xE)
        val x' = Context.fresh (H, x)
        val H' = Context.insert H x' Visibility.Visible (Context.rebind H A)
        val E' = subst (``x') x E
      in
        (H', x', E')
      end

    fun mkEvidence operator = fn Ds => operator $$ Vector.fromList Ds

    fun BY (Ds, V) = (Ds, V)
    infix BY

    fun @@ (H, (x,A)) = Context.insert H x Visibility.Visible A
    infix 8 @@

    fun asApp M =
      case out M of
           O $ ES => (O, ES)
         | _ => raise Refine

    fun ^! (M, O) =
      case out M of
           O' $ ES => if Operator.eq (O, O') then ES else raise Refine
         | _ => raise Refine
    infix ^!

    fun asVariable M =
      case out M of
           ` x => x
         | _ => raise Refine

    fun unify M N =
      if Syntax.eq (M, N) then
        M
      else
        raise Refine

    fun assertSubtype_ f H A B =
      if Syntax.eq (A, B) then
        A
      else
        case (out A, out B) of
             (SUBSET $ #[S,xT], SUBSET $ #[S',xT']) =>
               let
                 val S'' = f H S S'
                 val (H', x, T) = ctxUnbind (H,S'',xT)
                 val T' = xT' // ``x
               in
                 SUBSET $$ #[S'', f H' T T']
               end
           | (SUBSET $ #[S,xT], _) => f H S B
           | (FUN $ #[S, xT], FUN $ #[S', xT']) =>
               let
                 val S'' = f H S' S
                 val (H', x, T) = ctxUnbind (H, S'', xT)
                 val T' = xT' // ``x
               in
                 FUN $$ #[S'', f H' T T']
               end
           | _ => raise Refine

    fun typeLub H A B =
      assertSubtype_ typeLub H A B
      handle _ => assertSubtype_ typeLub H B A

    fun operatorIrrelevant O =
      case O of
           EQ => true
         | MEM => true
         | UNIT => true
         | VOID => true
         | CEQUAL => true
         | _ => false

    fun assertIrrelevant (H, P) =
      case out P of
           O $ _ => if operatorIrrelevant O then () else raise Refine
         | _ => raise Refine

    fun inferLevel (H, P) =
      case out P of
           UNIV l $ _ => Level.succ l
         | FUN $ #[A, xB] =>
           let
             val (H', x, B) = ctxUnbind (H, A, xB)
           in
             Level.max (inferLevel (H, A), inferLevel (H', B))
           end
         | PROD $ #[A, xB] =>
           let
             val (H', x, B) = ctxUnbind (H, A, xB)
           in
             Level.max (inferLevel (H, A), inferLevel (H', B))
           end
         | ISECT $ #[A, xB] =>
           let
             val (H', x, B) = ctxUnbind (H, A, xB)
           in
             Level.max (inferLevel (H, A), inferLevel (H', B))
           end
         | SUBSET $ #[A, xB] =>
           let
             val (H', x, B) = ctxUnbind (H, A, xB)
           in
             Level.max (inferLevel (H, A), inferLevel (H', B))
           end
         | ` x =>
            let
              val X = Context.lookup H x
              val k = inferLevel (H, X)
            in
              Level.pred k
            end
         | CUSTOM _ $ _ =>
             raise Refine
         | _ => Level.base

    fun inferType (H, M) =
      case out M of
           UNIV l $ _ => UNIV (Level.succ l) $$ #[]
         | AP $ #[F, N] =>
             let
               val #[A, xB] = inferType (H, F) ^! FUN
             in
               xB // N
             end
         | SPREAD $ #[X, uvE] =>
             let
               val #[A, xB] = inferType (H, X) ^! PROD
               val (H', u, vE) = ctxUnbind (H, A, uvE)
               val (H'', v, E) = ctxUnbind (H', xB // ``u, vE)

               val uval = SPREAD $$ #[X, u \\ (v \\ (``u))]
               val vval = SPREAD $$ #[X, u \\ (v \\ (``v))]
             in
               subst uval u (subst vval v (inferType (H'', E)))
             end
         | ` x => Context.lookup H x
         | _ => raise Refine

    fun Cum ok : tactic =
      fn (H >> P) =>
        let
          val #[A, B, univ] = P ^! EQ
          val (UNIV l, #[]) = asApp univ
          val k = case ok of NONE => Level.max (inferLevel (H, A), inferLevel (H, B)) | SOME k => k
          val _ = Level.assertLt (k, l)
        in
          [H >> EQ $$ #[A,B, UNIV k $$ #[]]] BY mkEvidence CUM
        end

    fun UnivEq (H >> P) =
      let
        val #[univ1, univ2, univ3] = P ^! EQ
        val (UNIV l, #[]) = asApp univ1
        val (UNIV l', #[]) = asApp univ2
        val (UNIV k, #[]) = asApp univ3
        val _ = Level.assertEq (l, l')
        val _ = Level.assertLt (l, k)
      in
        [] BY mkEvidence (UNIV_EQ l)
      end

    fun EqEq (H >> P) =
      let
        val #[E1, E2, univ] = P ^! EQ
        val (UNIV k, #[]) = asApp univ
        val #[M,N,A] = E1 ^! EQ
        val #[M',N',A'] = E2 ^! EQ
      in
        [ H >> EQ $$ #[A,A',univ]
        , H >> EQ $$ #[M,M',A]
        , H >> EQ $$ #[N,N',A]
        ] BY mkEvidence EQ_EQ
      end

    fun UnitIntro (H >> P) =
      let
        val #[] = P ^! UNIT
      in
        [] BY mkEvidence UNIT_INTRO
      end

    fun UnitElim i (H >> P) =
      let
        val x = Context.nth H (i - 1)
        val #[] = Context.lookup H x ^! UNIT
        val ax = AX $$ #[]
        val H' = ctxSubst H ax x
        val P' = subst ax x P
      in
        [ H' >> P'
        ] BY (fn [D] => UNIT_ELIM $$ #[`` x, D]
               | _ => raise Refine)
      end

    fun UnitEq (H >> P) =
      let
        val #[unit, unit', univ] = P ^! EQ
        val #[] = unit ^! UNIT
        val #[] = unit' ^! UNIT
        val (UNIV _, #[]) = asApp univ
      in
        [] BY mkEvidence UNIT_EQ
      end

    fun VoidEq (H >> P) =
      let
        val #[void, void', univ] = P ^! EQ
        val #[] = void ^! VOID
        val #[] = void' ^! VOID
        val (UNIV _, #[]) = asApp univ
      in
        [] BY mkEvidence VOID_EQ
      end

    fun VoidElim (H >> P) =
      [ H >> VOID $$ #[]
      ] BY mkEvidence VOID_ELIM

    fun AxEq (H >> P) =
      let
        val #[ax, ax', unit] = P ^! EQ
        val #[] = ax ^! AX
        val #[] = ax' ^! AX
        val #[] = unit ^! UNIT
      in
        [] BY mkEvidence AX_EQ
      end

    fun QuantifierEq (Q, Q_EQ) oz (H >> P) =
      let
        val #[q1, q2, univ] = P ^! EQ
        val #[A, xB] = q1 ^! Q
        val #[A', yB'] = q2 ^! Q
        val (UNIV _, #[]) = asApp univ

        val z =
          Context.fresh (H,
            case oz of
                 NONE => #1 (unbind xB)
               | SOME z => z)
      in
        [ H >> EQ $$ #[A,A',univ]
        , H @@ (z,A) >> EQ $$ #[xB // ``z, yB' // `` z, univ]
        ] BY (fn [D, E] => Q_EQ $$ #[D, z \\ E]
               | _ => raise Refine)
      end

    val FunEq = QuantifierEq (FUN, FUN_EQ)

    fun FunIntro (oz, ok) (H >> P) =
      let
        val #[P1, xP2] = P ^! FUN
        val z =
          Context.fresh (H,
            case oz of
                 NONE => #1 (unbind xP2)
               | SOME z => z)
        val k = case ok of NONE => inferLevel (H, P1) | SOME k => k
      in
        [ H @@ (z,P1) >> xP2 // `` z
        , H >> MEM $$ #[P1, UNIV k $$ #[]]
        ] BY (fn [D,E] => FUN_INTRO $$ #[z \\ D, E]
               | _ => raise Refine)
      end

    fun FunElim (i, s, onames) (H >> P) =
      let
        val s = Context.rebind H s
        val f = Context.nth H (i - 1)
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
      end

    fun LamEq (oz, ok) (H >> P) =
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
        val k = case ok of NONE => inferLevel (H, A) | SOME k => k
      in
        [ H @@ (z,A) >> EQ $$ #[aE // ``z, bE' // ``z, cB // ``z]
        , H >> MEM $$ #[A, UNIV k $$ #[]]
        ] BY (fn [D, E] => LAM_EQ $$ #[z \\ D, E]
                | _ => raise Refine)
      end

    fun FunExt (oz, ok) (H >> P) =
      let
        val #[f1,f2,funty] = P ^! EQ
        val #[S,xT] = funty ^! FUN
        val z =
          Context.fresh (H,
            case oz of
                 NONE => #1 (unbind xT)
               | SOME z => z)
        val k = case ok of NONE => inferLevel (H, S) | SOME k => k
      in
        [ H @@ (z, S) >> EQ $$ #[AP $$ #[f1,``z], AP $$ #[f2, ``z], xT // ``z]
        , H >> MEM $$ #[S, UNIV k $$ #[]]
        , H >> MEM $$ #[f1, funty]
        , H >> MEM $$ #[f2, funty]
        ] BY (fn [D,E,F,G] => FUN_EXT $$ #[z \\ D, E, F, G]
               | _ => raise Refine)
      end

    fun ApEq ofunty (H >> P) =
      let
        val #[f1t1, f2t2, Tt1] = P ^! EQ
        val #[f1, t1] = f1t1 ^! AP
        val #[f2, t2] = f2t2 ^! AP
        val funty =
          case ofunty of
               NONE => typeLub H (inferType (H, f1)) (inferType (H, f2))
             | SOME funty => Context.rebind H funty
        val #[S, xT] = funty ^! FUN
        val Tt1' = unify (xT // t1) Tt1
      in
        [ H >> EQ $$ #[f1, f2, funty]
        , H >> EQ $$ #[t1, t2, S]
        ] BY mkEvidence AP_EQ
      end

    val IsectEq = QuantifierEq (ISECT, ISECT_EQ)

    fun IsectIntro (oz, ok) (H >> P) =
      let
        val #[P1, xP2] = P ^! ISECT
        val z =
          Context.fresh (H,
            case oz of
                 NONE => #1 (unbind xP2)
               | SOME z => z)
        val k = case ok of NONE => inferLevel (H, P1) | SOME k => k
        val H' = Context.insert H z Visibility.Hidden P1
      in
        [ H' >> xP2 // `` z
        , H >> MEM $$ #[P1, UNIV k $$ #[]]
        ] BY (fn [D,E] => ISECT_INTRO $$ #[z \\ D, E]
               | _ => raise Refine)
      end

    fun IsectElim (i, s, onames) (H >> P) =
      let
        val s = Context.rebind H s
        val f = Context.nth H (i - 1)
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
      end

    fun IsectMemberEq (oz, ok) (H >> P) =
      let
        val #[M,N,A] = P ^! EQ
        val #[P1, xP2] = A ^! ISECT
        val z =
          Context.fresh (H,
            case oz of
                 NONE => #1 (unbind xP2)
               | SOME z => z)
        val k = case ok of NONE => inferLevel (H, P1) | SOME k => k
        val H' = Context.insert H z Visibility.Hidden P1
      in
        [ H' >> EQ $$ #[M,N, xP2 // ``z]
        , H >> MEM $$ #[P1, UNIV k $$ #[]]
        ] BY (fn [D, E] => ISECT_MEMBER_EQ $$ #[z \\ D, E]
               | _ => raise Refine)
      end

    fun IsectMemberCaseEq (oisect, t) (H >> P) =
      let
        val t = Context.rebind H t
        val #[F1,F2, Tt] = P ^! EQ
        val isect =
          case oisect of
               SOME isect => isect
             | NONE => typeLub H (inferType (H, F1)) (inferType (H, F2))

        val #[S, xT] = isect ^! ISECT
        val _ = unify Tt (xT // t)
      in
        [ H >> EQ $$ #[F1, F2, isect]
        , H >> MEM $$ #[t, S]
        ] BY mkEvidence ISECT_MEMBER_CASE_EQ
      end

    val SubsetEq = QuantifierEq (SUBSET, SUBSET_EQ)

    fun SubsetIntro (w, oz, ok) (H >> P) =
      let
        val w = Context.rebind H w
        val #[P1, xP2] = P ^! SUBSET
        val k = case ok of SOME k => k | NONE => inferLevel (H, P)
        val z =
          Context.fresh (H,
            case oz of
                 SOME z => z
               | NONE => #1 (unbind xP2))
      in
        [ H >> MEM $$ #[ w, P1]
        , H >> xP2 // w
        , H @@ (z, P1) >> MEM $$ #[xP2 // ``z, UNIV k $$ #[]]
        ] BY (fn [D, E, F] => SUBSET_INTRO $$ #[w, D, E, z \\ F]
               | _ => raise Refine)
      end

    fun IndependentSubsetIntro (H >> P) =
      let
        val #[P1, xP2] = P ^! SUBSET
        val (x, P2) = unbind xP2
        val _ = if hasFree (P2, x) then raise Refine else ()
      in
        [ H >> P1
        , H >> P2
        ] BY mkEvidence IND_SUBSET_INTRO
      end

    fun SubsetElim_ (z : Sequent.name, onames) (H >> P) =
      let
        val #[S, xT] = Context.lookup H z ^! SUBSET
        val (s, t) =
          case onames of
               SOME names => names
             | NONE =>
                 (Context.fresh (H, #1 (unbind xT)),
                  Context.fresh (H, Variable.named "t"))

        val G = Context.empty @@ (s, S)
        val G' = Context.insert G t Visibility.Hidden (xT // ``s)
        val H' = ctxSubst (Context.interposeAfter H (z, G')) (``s) z
        val P' = subst (``s) z P
      in
        [ H' >> P'
        ] BY (fn [D] => SUBSET_ELIM $$ #[``z, s \\ (t \\ D)]
               | _ => raise Refine)
      end

    fun SubsetElim (i, onames) (H >> P) =
      SubsetElim_ (Context.nth H (i - 1), onames) (H >> P)

    fun SubsetMemberEq (oz, ok) (H >> P) =
      let
        val #[s,t,subset] = P ^! EQ
        val #[S,xT] = subset ^! SUBSET
        val z =
          Context.fresh (H,
            case oz of
                 NONE => #1 (unbind xT)
               | SOME z => z)
        val k = case ok of SOME k => k | NONE => inferLevel (H, subset)
      in
        [ H >> EQ $$ #[s,t,S]
        , H >> xT // s
        , H @@ (z,S) >> MEM $$ #[xT // ``z, UNIV k $$ #[]]
        ] BY (fn [D, E, F] => SUBSET_MEMBER_EQ $$ #[D, E, z \\ F]
               | _ => raise Refine)
      end

    fun BaseEq (H >> P) =
      let
        val #[M, N, U] = P ^! EQ
        val #[] = M ^! BASE
        val #[] = N ^! BASE
        val (UNIV _, _) = asApp U
      in
        [] BY (fn [] => BASE_EQ $$ #[]
                | _ => raise Refine)
      end

    fun BaseIntro (H >> P) =
      let
        val #[] = P ^! BASE
      in
        [] BY (fn [] => BASE_INTRO $$ #[]
                | _ => raise Refine)
      end

    fun BaseMemberEq (H >> P) =
      let
        val #[M, N, U] = P ^! EQ
        val #[] = U ^! BASE
      in
        [H >> CEQUAL $$ #[M, N]
        ] BY (fn [D] => BASE_MEMBER_EQ $$ #[D]
               | _ => raise Refine)
      end

    fun BaseElimEq (i, z) (H >> P) =
      let
        val eq = Context.nth H (i - 1)
        val #[M, N, U] = Context.lookup H eq ^! EQ
        val #[] = U ^! BASE
        val z =
            case z of
                SOME z => z
              | NONE => Context.fresh (H, Variable.named "H")
      in
        [H @@ (z, CEQUAL $$ #[M, N]) >> P
        ] BY (fn [D] => BASE_ELIM_EQ $$ #[z \\ D]
               | _ => raise Refine)
      end

    fun MemCD (H >> P) =
      let
        val #[M, A] = P ^! MEM
      in
        [ H >> EQ $$ #[M, M, A]
        ] BY (fn [D] => D
               | _ => raise Refine)
      end

    fun Witness M (H >> P) =
      let
        val M = Context.rebind H M
        val hasHiddenVariables =
          foldl
            (fn (x, b) => b orelse #2 (Context.lookupVisibility H x) = Visibility.Hidden handle _ => false)
            false
            (freeVariables M)
        val _ =
          if hasHiddenVariables then
            assertIrrelevant (H, P)
          else
            ()
      in
        [ H >> MEM $$ #[M, P]
        ] BY (fn [D] => WITNESS $$ #[M, D]
               | _ => raise Refine)
      end

    fun HypEq (goal as H >> P) =
      let
        val P = P
        val #[M, M', A] = P ^! EQ
        val x = asVariable (unify M M')
        val _ = unify A (Context.lookup H x)
      in
        [] BY (fn _ => HYP_EQ $$ #[`` x])
      end

    val ProdEq = QuantifierEq (PROD, PROD_EQ)

    fun ProdIntro (w, oz, ok) (H >> P) =
      let
        val w = Context.rebind H w
        val #[P1, xP2] = P ^! PROD
        val k = case ok of SOME k => k | NONE => inferLevel (H, P)
        val z =
          Context.fresh (H,
            case oz of
                 SOME z => z
               | NONE => #1 (unbind xP2))
      in
        [ H >> MEM $$ #[w, P1]
        , H >> xP2 // w
        , H @@ (z, P1) >> MEM $$ #[xP2 // ``z, UNIV k $$ #[]]
        ] BY (fn [D, E, F] => PROD_INTRO $$ #[w, D, E, z \\ F]
               | _ => raise Refine)
      end

    fun IndependentProdIntro (H >> P) =
      let
        val #[P1, xP2] = P ^! PROD
        val (x, P2) = unbind xP2
        val _ = if hasFree (P2, x) then raise Refine else ()
      in
        [ H >> P1
        , H >> P2
        ] BY mkEvidence IND_PROD_INTRO
      end

    fun ProdElim (i, onames) (H >> P) =
      let
        val z = Context.nth H (i - 1)
        val #[S, xT] = Context.lookup H z ^! PROD
        val (s, t) =
          case onames of
               SOME names => names
             | NONE =>
                 (Context.fresh (H, Variable.named "s"),
                  Context.fresh (H, Variable.named "t"))

        val st = PAIR $$ #[``s, ``t]
        val J = Context.empty @@ (s, S) @@ (t, (xT // ``s))
        val H' = ctxSubst (Context.interposeAfter H (z, J)) st z
      in
        [ H' >> subst st z P
        ] BY (fn [D] => PROD_ELIM $$ #[``z, s \\ (t \\ D)]
               | _ => raise Refine)
      end

    fun PairEq (oz, ok) (H >> P) =
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
        val k = case ok of NONE => inferLevel (H, A) | SOME k => k
      in
        [ H >> EQ $$ #[M, M', A]
        , H >> EQ $$ #[N, N', xB // M]
        , H @@ (z,A) >> MEM $$ #[xB // `` z, UNIV k $$ #[]]
        ] BY (fn [D,E,F] => PAIR_EQ $$ #[D, E, z \\ F]
               | _ => raise Refine)
      end

    fun SpreadEq (ozC, oprod, onames) (H >> P) =
      let
        val #[spread, spread', CE1] = P ^! EQ
        val #[E1, xyT1] = spread ^! SPREAD
        val #[E2, uvT2] = spread' ^! SPREAD

        val prod =
          case oprod of
               NONE => typeLub H (inferType (H, E1)) (inferType (H, E2))
             | SOME prod => Context.rebind H prod

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
                   typeLub H'
                     (inferType (H', SPREAD $$ #[``z, xyT1]))
                     (inferType (H', SPREAD $$ #[``z, uvT2]))
               in
                 z \\ Cz
               end
             | SOME zC => Context.rebind H zC

        val CE1' = unify CE1 (zC // E1)
        val Ts = xT // ``s
        val st = PAIR $$ #[``s, ``t]
        val E1pair = EQ $$ #[E1, st, prod]
        val Cst = zC // st
        val T1st = (xyT1 // ``s) // ``t
        val T2st = (uvT2 // ``s) // ``t
      in
        [ H >> EQ $$ #[E1, E2, prod]
        , H @@ (s, S) @@ (t, Ts) @@ (y, E1pair) >> EQ $$ #[T1st, T2st, Cst]
        ] BY (fn [D, E] => SPREAD_EQ $$ #[D, s \\ (t \\ (y \\ E))]
                | _ => raise Refine)
      end


    fun PlusEq (H >> P) =
      let
        val #[L, R, U] = P ^! EQ
        val (UNIV _, #[]) = asApp U
        val #[A, B] = L ^! PLUS
        val #[A', B'] = R ^! PLUS
      in
         [ H >> EQ $$ #[A, A', U]
         , H >> EQ $$ #[B, B', U]
         ] BY (fn [L, R] => PLUS_EQ $$ #[L, R]
                | _ => raise Refine)
      end

    fun PlusIntroL x (H >> P) =
      let
        val #[A, B] = P ^! PLUS
        val k = case x of SOME k => k | NONE => inferLevel (H, B)
      in
        [ H >> A
        , H >> MEM $$ #[B, UNIV k $$ #[]]
        ] BY (fn [InA, WfB] => PLUS_INTROL $$ #[InA, WfB]
               | _ => raise Refine)
      end

    fun PlusIntroR x (H >> P) =
      let
        val #[A, B] = P ^! PLUS
        val k = case x of SOME k => k | NONE => inferLevel (H, A)
      in
        [ H >> B
        , H >> MEM $$ #[A, UNIV k $$ #[]]
        ] BY (fn [InB, WfA] => PLUS_INTROR $$ #[InB, WfA]
               | _ => raise Refine)
      end

    fun PlusElim (i, onames) (H >> P) =
      let
        val z = Context.nth H (i - 1)
        val #[A, B] = Context.lookup H z ^! PLUS
        val (s, t) =
            case onames of
                SOME names => names
              | NONE => (Context.fresh (H, Variable.named "s"),
                         Context.fresh (H, Variable.named "t"))
        val withs = INL $$ #[``s]
        val witht = INR $$ #[``t]
        val H's = ctxSubst (Context.interposeAfter H (z, Context.empty @@ (s, A)))
                           withs z
        val H't = ctxSubst (Context.interposeAfter H (z, Context.empty @@ (t, B)))
                           witht z
      in
        [ H's >> subst withs z P
        , H't >> subst witht z P
        ] BY (fn [L, R] => PLUS_ELIM $$ #[``z, s \\ L, t \\ R]
               | _ => raise Refine)
      end

    fun InlEq x (H >> P) =
      let
        val #[M, N, T] = P ^! EQ
        val #[A, B] = T ^! PLUS
        val #[M'] = M ^! INL
        val #[N'] = N ^! INL
        val k = case x of SOME k => k | NONE => inferLevel (H, B)
      in
        [ H >> EQ $$ #[M', N', A]
        , H >> MEM $$ #[B, UNIV k $$ #[]]
        ] BY (fn [In, Wf] => INL_EQ $$ #[In, Wf]
               | _ => raise Refine)
      end

    fun InrEq x (H >> P) =
      let
        val #[M, N, T] = P ^! EQ
        val #[A, B] = T ^! PLUS
        val #[M'] = M ^! INR
        val #[N'] = N ^! INR
        val k = case x of SOME k => k | NONE => inferLevel (H, A)
      in
        [ H >> EQ $$ #[M', N', B]
        , H >> MEM $$ #[A, UNIV k $$ #[]]
        ] BY (fn [In, Wf] => INR_EQ $$ #[In, Wf]
               | _ => raise Refine)
      end

    fun DecideEq C (A, B, x) (H >> P) =
      let
        val #[M, N, T] = P ^! EQ
        val #[M', sL, tR] = M ^! DECIDE
        val #[N', sL', tR'] = N ^! DECIDE
        val (s, t, eq) =
            case x of
                SOME names => names
              | NONE => (Context.fresh (H, Variable.named "s"),
                         Context.fresh (H, Variable.named "t"),
                         Context.fresh (H, Variable.named "eq"))
        val H's = H @@ (s, A)
                    @@ (eq, EQ $$ #[M', INL $$ #[``s], PLUS $$ #[A, B]])
        val H't = H @@ (t, B)
                    @@ (eq, EQ $$ #[M', INR $$ #[``t], PLUS $$ #[A, B]])
        val C's = subst1 C (INL $$ #[``s])
        val C't = subst1 C (INR $$ #[``t])
      in
        [ H >> EQ $$ #[M', N', PLUS $$ #[A, B]]
        , H's >> EQ $$ #[subst1 sL (``s), subst1 sL' (``s), C's]
        , H't >> EQ $$ #[subst1 tR (``t), subst1 tR' (``t), C't]
        ] BY (fn [EqM, EqL, EqR] =>
                 DECIDE_EQ $$ #[EqM, eq \\ (s \\ EqR), eq \\ (t \\ EqL)]
               | _ => raise Refine)
      end

    fun Hypothesis_ x (H >> P) =
      let
        val (P', visibility) = Context.lookupVisibility H x
        val P'' = unify P P'
      in
        (case visibility of
             Visibility.Visible => ()
           | Visibility.Hidden => assertIrrelevant (H, P''));
        [] BY (fn _ => ``x)
      end

    fun Hypothesis i (H >> P) = Hypothesis_ (Context.nth H (i - 1)) (H >> P)

    fun Assumption (H >> P) =
      case Context.search H (fn x => Syntax.eq (P, x)) of
           SOME (x, _) => Hypothesis_ x (H >> P)
         | NONE => raise Refine

    fun Assert (term, name) (H >> P) =
      let
        val z =
            case name of
                SOME z => z
              | NONE => Context.fresh (H, Variable.named "H")
        val term' = Context.rebind H term
      in
        [ H >> term'
        , H @@ (z, term') >> P
        ] BY (fn [D, E] => ASSERT $$ #[D, z \\ E]
               | _ => raise Refine)
      end

    structure LevelSolver =
      LevelSolver
        (SyntaxWithUniverses
          (type label = Development.label
           structure Syntax = Syntax))

    structure SequentLevelSolver = SequentLevelSolver
      (structure Solver = LevelSolver
       structure Abt = Syntax
       structure Sequent = Sequent)

    fun Unfolds (development, lbls) (H >> P) =
      let
        open Conversionals
        infix CTHEN
        val conv =
          foldl (fn ((lbl, ok), acc) =>
            let
              val k = case ok of SOME k => k | NONE => Level.base
              val conv =
                LevelSolver.subst (LevelSolver.Level.yank k)
                  o CDEEP (Development.lookupDefinition development lbl)
            in
              acc CTHEN conv
            end) CID lbls
      in
        [ Context.map conv H >> conv P
        ] BY (fn [D] => D
               | _ => raise Refine)
      end

    fun Lemma (development, lbl) (H >> P) =
      let
        val {statement, evidence} = Development.lookupTheorem development lbl
        val H' >> P' = statement
        val constraints = SequentLevelSolver.generateConstraints (statement, H >> P)
        val substitution = LevelSolver.Level.resolve constraints
        val shovedEvidence = LevelSolver.subst substitution (Susp.force evidence)
      in
        [] BY (fn _ => shovedEvidence)
      end

    fun Admit (H >> P) =
      [] BY (fn _ => ADMIT $$ #[])

    fun RewriteGoal (c : conv) (H >> P) =
      [ Context.map c H >> c P
      ] BY (fn [D] => D | _ => raise Refine)

    fun EqSym (H >> P) =
      let
        val #[M,N,A] = P ^! EQ
      in
        [ H >> EQ $$ #[N,M,A]
        ] BY mkEvidence EQ_SYM
      end

    fun EqSubst (eq, xC, ok) (H >> P) =
      let
        val #[M,N,A] = Context.rebind H eq ^! EQ
        val (H', x, C) = ctxUnbind (H, A, xC)
        val P' = unify P (xC // M)
        val k = case ok of SOME k => k | NONE => inferLevel (H', C)
      in
        [ H >> eq
        , H >> xC // N
        , H' >> MEM $$ #[C, UNIV k $$ #[]]
        ] BY (fn [D,E,F] => EQ_SUBST $$ #[D, E, x \\ F]
               | _ => raise Refine)
      end

    local
      structure Tacticals = Tacticals (Lcf)
      open Tacticals
      infix THEN THENL
    in
      fun HypEqSubst (dir, i, xC, ok) (H >> P) =
        let
          val xC = Context.rebind H xC
          val z = Context.nth H (i - 1)
          val X = Context.lookup H z
        in
          case dir of
               Dir.RIGHT => (EqSubst (X, xC, ok) THENL [Hypothesis_ z, ID, ID]) (H >> P)
             | Dir.LEFT =>
                 let
                   val #[M,N,A] = X ^! EQ
                 in
                   (EqSubst (EQ $$ #[N,M,A], xC, ok)
                     THENL [EqSym THEN Hypothesis_ z, ID, ID]) (H >> P)
                 end
        end

      fun CEqEq (H >> P) =
        let
          val #[M, N, U] = P ^! EQ
          val (UNIV _, _) = asApp U
          val #[L, R] = M ^! CEQUAL
          val #[L', R'] = N ^! CEQUAL
        in
          [ H >> CEQUAL $$ #[L, L']
          , H >> CEQUAL $$ #[R, R']
          ] BY (fn [D, E] => CEQUAL_EQ $$ #[D, E]
                 | _ => raise Refine)
        end

      local
          fun bothStuck M N =
            (Semantics.step M; raise Refine)
            handle Semantics.Stuck _ =>
                   (Semantics.step N; raise Refine)
                   handle Semantics.Stuck _ => ()
      in
      fun CEqRefl (H >> P) =
        let
          val #[M, N] = P ^! CEQUAL
          val () = (unify M N; ()) handle Refine => bothStuck M N
        in
            [] BY (fn [] => CEQUAL_REFL $$ #[]
                   | _  => raise Refine)
        end
      end

      fun CEqSym (H >> P) =
        let
          val #[M, N] = P ^! CEQUAL
        in
          [H >> CEQUAL $$ #[N, M]
          ] BY (fn [D] => CEQUAL_SYM $$ #[D]
                 | _ => raise Refine)
        end

      fun CEqStep (H >> P) =
        let
          val #[M, N] = P ^! CEQUAL
          val M' =
              case Semantics.step M handle Semantics.Stuck _ => raise Refine of
                  Semantics.STEP M' => M'
                | Semantics.CANON => raise Refine
                | Semantics.NEUTRAL => raise Refine
        in
          [ H >> CEQUAL $$ #[M', N]
          ] BY (fn [D] => CEQUAL_STEP $$ #[D]
                 | _ => raise Refine)
        end

      fun CEqSubst (eq, xC) (H >> P) =
        let
          val #[M, N] = eq ^! CEQUAL
          val _ = unify P (xC // M)
        in
          [ H >> eq
          , H >> xC // N
          ] BY (fn [D, E] => CEQUAL_SUBST $$ #[D, E]
                 | _ => raise Refine)
        end

      fun HypCEqSubst (dir, i, xC) (H >> P) =
        let
          val xC = Context.rebind H xC
          val z = Context.nth H (i - 1)
          val X = Context.lookup H z
        in
          case dir of
              Dir.RIGHT =>
              (CEqSubst (X, xC) THENL [Hypothesis_ z, ID]) (H >> P)
            | Dir.LEFT =>
              let
                val #[M,N] = X ^! CEQUAL
              in
                (CEqSubst (CEQUAL $$ #[N,M], xC)
                          THENL [CEqSym THEN Hypothesis_ z, ID]) (H >> P)
              end
        end

      local
        (* Create a new subgoal by walking along the pairs
         * of terms and unbind each term together. As we go
         * we add the new variables to the context as we go
         * and keep track of all the variables we bind.
         *
         * In the end you get a new goal and a list of variables in the
         * order that they were created.
         *)
        fun newSubGoal H vs (t1, t2) =
          case (out t1, out t2) of
              (x \ t1', y \ t2') =>
              newSubGoal (H @@ (x, BASE $$ #[]))
                         (x :: vs)
                         (t1', subst (``x) y t2')
            | (_, _) =>
              (List.rev vs, H >> CEQUAL $$ #[t1, t2])

        fun toList v = Vector.foldr op:: nil v

        (* Each derivation needs to bind the variables from the
         * context so all we do is take a vector of lists of variables
         * and a vector of terms and bind all the variables in one list
         * in the corresponding term.
         *)
        fun bindVars vars terms =
          let
            fun go [] t = t
              | go (v :: vs) t = go vs (v \\ t)
          in
            Vector.tabulate (Vector.length terms,
                             fn i => go (Vector.sub (vars, i))
                                        (Vector.sub (terms, i)))
          end

      in
      fun CEqStruct (H >> P) =
        let
          val #[M, N] = P ^! CEQUAL
          val (oper, subterms) = asApp M
          val subterms' = N ^! oper
          val pairs =
              Vector.tabulate (Vector.length subterms,
                               (fn i => (Vector.sub(subterms, i),
                                         Vector.sub(subterms', i))))
          val (boundVars, subgoals) =
              ListPair.unzip (toList (Vector.map (newSubGoal H []) pairs))
          val boundVars = Vector.fromList boundVars
        in
          subgoals BY (fn Ds =>
                          CEQUAL_STRUCT (Vector.map List.length boundVars)
                            $$ bindVars boundVars (Vector.fromList Ds)
                          handle _ => raise Refine)
        end
      end
    end

    local
      structure Tacticals = Tacticals(Lcf)
      open Tacticals infix THEN
    in
      fun EqInSupertype (H >> P) =
        let
          val #[M,N,A] = P ^! EQ
          val result =
            Context.search H (fn A' =>
              case out A' of
                   SUBSET $ #[A'', _] => Syntax.eq (A, A'')
                 | _ => false)
          val x = case result of SOME (x,_) => x | NONE => raise Refine
        in
          (SubsetElim_ (x, NONE) THEN HypEq) (H >> P)
        end
    end
  end

  structure Conversions =
  struct
    open Conversionals Conv

    val ApBeta : conv = reductionRule
      (fn AP $ #[LAM $ #[xE], N] => xE // into N
        | _ => raise Conv)

    val SpreadBeta : conv = reductionRule
      (fn SPREAD $ #[PAIR $ #[M,N], xyE] => (into xyE // M) // N
        | _ => raise Conv)

    val DecideBeta : conv = reductionRule
      (fn DECIDE $ #[INL $ #[E], N, M] => (into N // E)
        | DECIDE $ #[INR $ #[E], N, M] => (into M // E)
        | _ => raise Conv)
  end
end

structure Ctt = Ctt
  (structure Lcf = Lcf
   structure Syntax = Syntax
   structure Conv = Conv
   structure Semantics = Semantics
   structure Sequent = Sequent
   structure Development = Development)
