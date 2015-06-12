functor Ctt
  (structure Development : DEVELOPMENT
   structure Syntax : ABT_UTIL
    where type Operator.t = Development.label OperatorType.operator

   structure Sequent : SEQUENT
     where type term = Syntax.t
     where type Context.name = Syntax.Variable.t

   structure ConvTypes : CONV_TYPES where Syntax = Syntax

   sharing type Development.Lcf.goal = Sequent.sequent
   sharing type Development.Lcf.evidence = Syntax.t
   sharing Development.Telescope.Label = Syntax.Variable
   sharing type Development.term = Syntax.t) : CTT =
struct
  structure Lcf = Development.Lcf
  structure ConvTypes = ConvTypes
  structure Syntax = Syntax

  type tactic = Lcf.tactic
  type conv = ConvTypes.conv
  type name = Sequent.name
  type term = Syntax.t
  type goal = Sequent.sequent

  structure Operator = Syntax.Operator
  structure Development = Development
  structure Conversionals = Conversionals
    (structure Syntax = Syntax
     structure ConvTypes = ConvTypes)

  open Syntax
  open Operator OperatorType
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
         | UNIT => true
         | VOID => true
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
         | SUBSET $ #[A, xB] =>
           let
             val (H', x, B) = ctx_unbind (H, A, xB)
           in
             Level.max (infer_level (H, A), infer_level (H', B))
           end
         | ` x =>
            let
              val X = Context.lookup H x
              val k = infer_level (H, X)
            in
              k - 1
            end
         | CUSTOM _ $ _ =>
             raise Refine
         | _ => 0

    fun infer_type (H, M) =
      case out M of
           UNIV l $ _ => UNIV (l + 1) $$ #[]
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

               val uval = SPREAD $$ #[X, u \\ (v \\ (``u))]
               val vval = SPREAD $$ #[X, u \\ (v \\ (``v))]
             in
               subst uval u (subst vval v (infer_type (H'', E)))
             end
         | ` x => Context.lookup H x
         | _ => raise Refine

    fun Cum ok : tactic =
      fn (H >> P) =>
        let
          val #[A, B, univ] = P ^! EQ
          val (UNIV l, #[]) = as_app univ
          val k = case ok of NONE => Level.max (infer_level (H, A), infer_level (H, B)) | SOME k => k
          val _ = Level.assert_lt (k, l)
        in
          [H >> EQ $$ #[A,B, UNIV k $$ #[]]] BY mk_evidence CUM
        end

    fun UnivEq (H >> P) =
      let
        val #[univ1, univ2, univ3] = P ^! EQ
        val (UNIV l, #[]) = as_app univ1
        val (UNIV l', #[]) = as_app univ2
        val (UNIV k, #[]) = as_app univ3
        val _ = Level.assert_lt (Level.unify (l, l'), k)
      in
        [] BY mk_evidence UNIV_EQ
      end

    fun EqEq (H >> P) =
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
      end

    fun UnitIntro (H >> P) =
      let
        val #[] = P ^! UNIT
      in
        [] BY mk_evidence UNIT_INTRO
      end

    fun UnitElim x (H >> P) =
      let
        val #[] = Context.lookup H x ^! UNIT
        val ax = AX $$ #[]
        val H' = ctx_subst H ax x
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
        val (UNIV _, #[]) = as_app univ
      in
        [] BY mk_evidence UNIT_EQ
      end

    fun VoidEq (H >> P) =
      let
        val #[void, void', univ] = P ^! EQ
        val #[] = void ^! VOID
        val #[] = void' ^! VOID
        val (UNIV _, #[]) = as_app univ
      in
        [] BY mk_evidence VOID_EQ
      end

    fun VoidElim (H >> P) =
      [ H >> VOID $$ #[]
      ] BY mk_evidence VOID_ELIM

    fun AxEq (H >> P) =
      let
        val #[ax, ax', unit] = P ^! EQ
        val #[] = ax ^! AX
        val #[] = ax' ^! AX
        val #[] = unit ^! UNIT
      in
        [] BY mk_evidence AX_EQ
      end

    fun QuantifierEq (Q, Q_EQ) oz (H >> P) =
      let
        val #[q1, q2, univ] = P ^! EQ
        val #[A, xB] = q1 ^! Q
        val #[A', yB'] = q2 ^! Q
        val (UNIV _, #[]) = as_app univ

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
        val k = case ok of NONE => infer_level (H, P1) | SOME k => k
      in
        [ H @@ (z,P1) >> xP2 // `` z
        , H >> MEM $$ #[P1, UNIV k $$ #[]]
        ] BY (fn [D,E] => FUN_INTRO $$ #[z \\ D, E]
               | _ => raise Refine)
      end

    fun FunElim (f, s, onames) (H >> P) =
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
        val k = case ok of NONE => infer_level (H, A) | SOME k => k
      in
        [ H @@ (z,A) >> EQ $$ #[aE // ``z, bE' // ``z, cB // ``z]
        , H >> MEM $$ #[A, UNIV k $$ #[]]
        ] BY (fn [D, E] => LAM_EQ $$ #[z \\ D, E]
                | _ => raise Refine)
      end

    fun ApEq ofunty (H >> P) =
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
        val k = case ok of NONE => infer_level (H, P1) | SOME k => k
        val H' = Context.insert H z Visibility.Hidden P1
      in
        [ H' >> xP2 // `` z
        , H >> MEM $$ #[P1, UNIV k $$ #[]]
        ] BY (fn [D,E] => ISECT_INTRO $$ #[z \\ D, E]
               | _ => raise Refine)
      end

    fun IsectElim (f, s, onames) (H >> P) =
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
        val k = case ok of NONE => infer_level (H, P1) | SOME k => k
        val H' = Context.insert H z Visibility.Hidden P1
      in
        [ H' >> EQ $$ #[M,N, xP2 // ``z]
        , H >> MEM $$ #[P1, UNIV k $$ #[]]
        ] BY (fn [D, E] => ISECT_MEMBER_EQ $$ #[z \\ D, E]
               | _ => raise Refine)
      end

    fun IsectMemberCaseEq (oisect, t) (H >> P) =
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
      end

    val SubsetEq = QuantifierEq (SUBSET, SUBSET_EQ)

    fun SubsetIntro (w, oz, ok) (H >> P) =
      let
        val #[P1, xP2] = P ^! SUBSET
        val k = case ok of SOME k => k | NONE => infer_level (H, P)
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
        val _ = if has_free (P2, x) then raise Refine else ()
      in
        [ H >> P1
        , H >> P2
        ] BY mk_evidence IND_SUBSET_INTRO
      end

    fun SubsetElim (z, onames) (H >> P) =
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
        val H' = ctx_subst (Context.interpose_after H (z, G')) (``s) z
        val P' = subst (``s) z P
      in
        [ H' >> P'
        ] BY (fn [D] => SUBSET_ELIM $$ #[``z, s \\ (t \\ D)]
               | _ => raise Refine)
      end

    fun SubsetMemberEq (oz, ok) (H >> P) =
      let
        val #[s,t,subset] = P ^! EQ
        val #[S,xT] = subset ^! SUBSET
        val z =
          Context.fresh (H,
            case oz of
                 NONE => #1 (unbind xT)
               | SOME z => z)
        val k = case ok of SOME k => k | NONE => infer_level (H, subset)
      in
        [ H >> EQ $$ #[s,t,S]
        , H >> xT // s
        , H @@ (z,S) >> MEM $$ #[xT // ``z, UNIV k $$ #[]]
        ] BY (fn [D, E, F] => SUBSET_MEMBER_EQ $$ #[D, E, z \\ F]
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
        val has_hidden_variables =
          foldl
            (fn (x, b) => b orelse #2 (Context.lookup_visibility H x) = Visibility.Hidden)
            false
            (free_variables M)
        val _ =
          if has_hidden_variables then
            assert_irrelevant (H, P)
          else
            ()
      in
        [ H >> MEM $$ #[M, P]
        ] BY (fn [D] => WITNESS $$ #[M, D]
               | _ => raise Refine)
      end

    fun HypEq (H >> P) =
      let
        val #[M, M', A] = P ^! EQ
        val x = as_variable (unify M M')
        val _ = unify A (Context.lookup H x)
      in
        [] BY (fn _ => HYP_EQ $$ #[`` x])
      end

    val ProdEq = QuantifierEq (PROD, PROD_EQ)

    fun ProdIntro (w, oz, ok) (H >> P) =
      let
        val #[P1, xP2] = P ^! PROD
        val k = case ok of SOME k => k | NONE => infer_level (H, P)
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
        val _ = if has_free (P2, x) then raise Refine else ()
      in
        [ H >> P1
        , H >> P2
        ] BY mk_evidence IND_PROD_INTRO
      end

    fun ProdElim (z, onames) (H >> P) =
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
        val k = case ok of NONE => infer_level (H, A) | SOME k => k
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
      in
        [ H >> EQ $$ #[E1, E2, prod]
        , H @@ (s, S) @@ (t, Ts) @@ (y, E1pair) >> EQ $$ #[T1st, T2st, Cst]
        ] BY (fn [D, E] => SPREAD_EQ $$ #[D, s \\ (t \\ (y \\ E))]
                | _ => raise Refine)
      end

    fun Hypothesis x (H >> P) =
      let
        val (P', visibility) = Context.lookup_visibility H x
        val P'' = unify P P'
      in
        (case visibility of
             Visibility.Visible => ()
           | Visibility.Hidden => assert_irrelevant (H, P''));
        [] BY (fn _ => ``x)
      end

    fun Assumption (H >> P) =
      case Context.search H (fn x => Syntax.eq (P, x)) of
           SOME (x, _) => Hypothesis x (H >> P)
         | NONE => raise Refine

    fun Unfold (development, lbl) (H >> P) =
      let
        open Conversionals
        val conv = CDEEP (Development.lookup_definition development lbl)
      in
        [ Context.map conv H >> conv P
        ] BY (fn [D] => D
               | _ => raise Refine)
      end

    fun Lemma (development, lbl) (H >> P) =
      let
        val {statement, evidence} = Development.lookup_theorem development lbl
        val H' >> P' = statement
      in
        if Context.subcontext Syntax.eq (H', H) andalso Syntax.eq (P, P')
        then [] BY (fn _ => Susp.force evidence)
        else raise Refine
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
        ] BY mk_evidence EQ_SYM
      end

    fun EqSubst (eq, xC, ok) (H >> P) =
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
      end

    datatype dir = LEFT | RIGHT
    local
      structure Tacticals = Tacticals (Lcf)
      open Tacticals
      infix THEN THENL
    in
      fun HypEqSubst (dir, z, xC, ok) (H >> P) =
        let
          val X = Context.lookup H z
        in
          case dir of
               RIGHT => (EqSubst (X, xC, ok) THENL [Hypothesis z, ID, ID]) (H >> P)
             | LEFT =>
                 let
                   val #[M,N,A] = X ^! EQ
                 in
                   (EqSubst (EQ $$ #[N,M,A], xC, ok)
                     THENL [EqSym THEN Hypothesis z, ID, ID]) (H >> P)
                 end
        end
    end
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
   structure ConvTypes = ConvTypes
   structure Sequent = Sequent
   structure Development = Development)
