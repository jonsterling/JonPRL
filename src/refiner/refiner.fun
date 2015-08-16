functor Refiner
  (structure Syntax : ABT_UTIL
     where type Operator.t = UniversalOperator.t
   structure Sequent : SEQUENT
     where type term = Syntax.t
     where Context.Syntax = Syntax
   structure Lcf : LCF
     where type evidence = Syntax.t
     where type goal = Sequent.sequent Goal.goal

   structure Development : DEVELOPMENT
     where type judgement = Sequent.sequent
     where type evidence = Lcf.evidence
     where type tactic = Lcf.tactic
     where type operator = UniversalOperator.t

   structure Conv : CONV where type term = Syntax.t
   structure Semantics : SMALL_STEP where type syn = Syntax.t
   sharing type Development.term = Syntax.t
   structure Builtins : BUILTINS
     where type Conv.term = Conv.term) : REFINER =
struct
  structure Lcf = Lcf
  structure Conv = ConvUtil(structure Conv = Conv and Syntax = Syntax)
  structure Syntax = Syntax

  structure Sequent = Sequent
  structure Development = Development

  type tactic = Lcf.tactic
  type conv = Conv.conv
  type name = Sequent.name
  type term = Syntax.t
  type goal = Sequent.sequent

  type operator = Syntax.Operator.t
  type hyp = name HypSyn.t

  structure Operator = Syntax.Operator
  structure Conversionals = Conversionals
    (structure Syntax = Syntax
     structure Conv = Conv)

  open Syntax CttCalculus Derivation
  structure C = CttCalculusInj and D = DerivationInj

  type world = Development.world

  structure CttCalculusView = RestrictAbtView
    (structure Abt = Syntax
     structure Injection = CttCalculusInj)


  infix $ \
  infix 8 $$ //
  infixr 8 \\

  exception Refine

  structure Rules =
  struct
    open Goal Sequent
    infix 3 >>
    infix 2 |:

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

    (* assert that an expression's free variables are all bound in context *)
    fun assertClosed (H : context) (m : Syntax.t) =
      let
        val FVs = Syntax.freeVariables m
        val isClosed = List.all (fn x => case Context.find H x of NONE => false | SOME _ => true) FVs
      in
        if isClosed then
          ()
        else
          raise Fail "Expression contains variables not bound in context"
      end


    fun mkEvidence operator = fn Ds => D.`> operator $$ Vector.fromList Ds

    fun BY (Ds, V) = (Ds, V)
    infix BY

    fun @@ (H, (x,A)) = Context.insert H x Visibility.Visible A
    infix 8 @@

    fun asApp M =
      case out M of
           theta $ ES => (C.`< theta, ES)
         | _ => raise Refine

    fun ^! (M, theta) =
      case out M of
           theta' $ ES => if Operator.eq (C.`> theta, theta') then ES else raise Refine
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

    local
      open CttCalculusView
    in
      fun assertSubtype_ f H A B =
        if Syntax.eq (A, B) then
          A
        else
          case (project A, project B) of
               (SUBSET $ #[S,xT], SUBSET $ #[S',xT']) =>
                 let
                   val S'' = f H S S'
                   val (H', x, T) = ctxUnbind (H,S'',xT)
                   val T' = xT' // ``x
                 in
                   C.`> SUBSET $$ #[S'', f H' T T']
                 end
             | (SUBSET $ #[S,xT], _) => f H S B
             | (FUN $ #[S, xT], FUN $ #[S', xT']) =>
                 let
                   val S'' = f H S' S
                   val (H', x, T) = ctxUnbind (H, S'', xT)
                   val T' = xT' // ``x
                 in
                   C.`> FUN $$ #[S'', f H' T T']
                 end
             | _ => raise Refine
    end

    fun typeLub H A B =
      assertSubtype_ typeLub H A B
      handle _ => assertSubtype_ typeLub H B A

    fun operatorIrrelevant theta =
      case theta of
           EQ => true
         | MEM => true
         | UNIT => true
         | VOID => true
         | CEQUAL => true
         | APPROX => true
         | SQUASH => true
         | HASVALUE => true
         | _ => false

    fun assertIrrelevant (H, P) =
      case out P of
           theta $ _ => if operatorIrrelevant (C.`< theta) then () else raise Refine
         | _ => raise Refine

    fun eliminationTarget hyp (H >> P) =
      let
        val z =
          case hyp of
               HypSyn.INDEX i => Context.nth H (i - 1)
             | HypSyn.NAME z => Context.rebindName H z
        val (A, visibility) = Context.lookupVisibility H z
      in
        case visibility of
             Visibility.Hidden =>
              (assertIrrelevant (H, P); z)
           | Visibility.Visible => z
      end

    local
      open CttCalculusView
    in
      fun inferLevel (H, P) =
        case project P of
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
           | EQ $ #[M,N,A] => inferLevel (H, A)
           | MEM $ #[M,A] => inferLevel (H, A)
           | ` x =>
              let
                val X = Context.lookup H x
                val k = inferLevel (H, X)
              in
                Level.pred k
              end
           | _ => Level.base

      fun inferType (H, M) =
        case project M of
             UNIV l $ _ => C.`> (UNIV (Level.succ l)) $$ #[]
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

                 val uval = C.`> SPREAD $$ #[X, u \\ (v \\ (``u))]
                 val vval = C.`> SPREAD $$ #[X, u \\ (v \\ (``v))]
               in
                 subst uval u (subst vval v (inferType (H'', E)))
               end
           | ` x => Context.lookup H x
           | _ => raise Refine
    end

    fun Cum ok : tactic =
      fn (_ |: H >> P) =>
        let
          val #[A, B, univ] = P ^! EQ
          val (UNIV l, #[]) = asApp univ
          val k = case ok of NONE => Level.max (inferLevel (H, A), inferLevel (H, B)) | SOME k => k
          val _ = Level.assertLt (k, l)
        in
          [MAIN |: H >> C.`> EQ $$ #[A,B, C.`> (UNIV k) $$ #[]]] BY mkEvidence CUM
        end

    fun UnivEq (_ |: H >> P) =
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

    fun EqEq (_ |: H >> P) =
      let
        val #[E1, E2, univ] = P ^! EQ
        val (UNIV k, #[]) = asApp univ
        val #[M,N,A] = E1 ^! EQ
        val #[M',N',A'] = E2 ^! EQ
      in
        [ MAIN |: H >> C.`> EQ $$ #[A,A',univ]
        , MAIN |: H >> C.`> EQ $$ #[M,M',A]
        , MAIN |: H >> C.`> EQ $$ #[N,N',A]
        ] BY mkEvidence EQ_EQ
      end

    fun EqEqBase (_ |: H >> P) =
      let
        val #[E1, E2, univ] = P ^! EQ
        val (UNIV k, #[]) = asApp univ
        val #[M,N,A] = E1 ^! EQ
        val #[M',N',A'] = E2 ^! EQ
        val bas = C.`> BASE $$ #[]
        val img = C.`> BUNION $$ #[A, bas]
      in
        [ MAIN |: H >> C.`> EQ $$ #[A,A',univ]
        , MAIN |: H >> C.`> EQ $$ #[M,M',img]
        , MAIN |: H >> C.`> EQ $$ #[N,N',img]
        ] BY mkEvidence EQ_EQ_BASE
      end

    fun EqMemEq (_ |: H >> P) =
      let
        val #[M, N, E] = P ^! EQ
        val #[] = M ^! AX
        val #[] = N ^! AX
        val #[M', N', T] = E ^! EQ
      in
        [ MAIN |: H >> E
        ] BY mkEvidence EQ_MEMBER_EQ
      end

    fun QuantifierEq (Q, Q_EQ) oz (_ |: H >> P) =
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
        [ MAIN |: H >> C.`> EQ $$ #[A,A',univ]
        , MAIN |: H @@ (z,A) >> C.`> EQ $$ #[xB // ``z, yB' // `` z, univ]
        ] BY (fn [D, E] => D.`> Q_EQ $$ #[D, z \\ E]
               | _ => raise Refine)
      end

    val FunEq = QuantifierEq (FUN, FUN_EQ)

    fun FunIntro (oz, ok) (_ |: H >> P) =
      let
        val #[P1, xP2] = P ^! FUN
        val z =
          Context.fresh (H,
            case oz of
                 NONE => #1 (unbind xP2)
               | SOME z => z)
        val k = case ok of NONE => inferLevel (H, P1) | SOME k => k
      in
        [ MAIN |: H @@ (z,P1) >> xP2 // `` z
        , AUX |: H >> C.`> MEM $$ #[P1, C.`> (UNIV k) $$ #[]]
        ] BY (fn [D,E] => D.`> FUN_INTRO $$ #[z \\ D, E]
               | _ => raise Refine)
      end

    fun FunElim (hyp, s, onames) (_ |: H >> P) =
      let
        val s = Context.rebind H s
        val f = eliminationTarget hyp (H >> P)
        val #[S, xT] = Context.lookup H f ^! FUN
        val Ts = xT // s
        val (y, z) =
          case onames of
               SOME names => names
             | NONE =>
                 (Context.fresh (H, Variable.named "y"),
                  Context.fresh (H, Variable.named "z"))

        val fsTs = C.`> EQ $$ #[``y, C.`> AP $$ #[``f, s], Ts]
      in
        [ AUX |: H >> C.`> MEM $$ #[s, S]
        , MAIN |: H @@ (y, Ts) @@ (z, fsTs) >> P
        ] BY (fn [D, E] => D.`> FUN_ELIM $$ #[``f, s, D, y \\ (z \\ E)]
                | _ => raise Refine)
      end

    fun LamEq (oz, ok) (_ |: H >> P) =
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
        [ MAIN |: H @@ (z,A) >> C.`> EQ $$ #[aE // ``z, bE' // ``z, cB // ``z]
        , AUX |: H >> C.`> MEM $$ #[A, C.`> (UNIV k) $$ #[]]
        ] BY (fn [D, E] => D.`> LAM_EQ $$ #[z \\ D, E]
                | _ => raise Refine)
      end

    fun FunExt (oz, ok) (_ |: H >> P) =
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
        [ MAIN |: H @@ (z, S) >> C.`> EQ $$ #[C.`> AP $$ #[f1,``z], C.`> AP $$ #[f2, ``z], xT // ``z]
        , AUX |: H >> C.`> MEM $$ #[S, C.`> (UNIV k) $$ #[]]
        , AUX |: H >> C.`> MEM $$ #[f1, funty]
        , AUX |: H >> C.`> MEM $$ #[f2, funty]
        ] BY (fn [D,E,F,G] => D.`> FUN_EXT $$ #[z \\ D, E, F, G]
               | _ => raise Refine)
      end

    fun ApEq ofunty (_ |: H >> P) =
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
        [ MAIN |: H >> C.`> EQ $$ #[f1, f2, funty]
        , MAIN |: H >> C.`> EQ $$ #[t1, t2, S]
        ] BY mkEvidence AP_EQ
      end

    val IsectEq = QuantifierEq (ISECT, ISECT_EQ)

    fun IsectIntro (oz, ok) (_ |: H >> P) =
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
        [ MAIN |: H' >> xP2 // `` z
        , AUX |: H >> C.`> MEM $$ #[P1, C.`> (UNIV k) $$ #[]]
        ] BY (fn [D,E] => D.`> ISECT_INTRO $$ #[z \\ D, E]
               | _ => raise Refine)
      end

    fun IsectElim (hyp, s, onames) (_ |: H >> P) =
      let
        val s = Context.rebind H s
        val f = eliminationTarget hyp (H >> P)

        val #[S, xT] = Context.lookup H f ^! ISECT
        val Ts = xT // s
        val (y, z) =
          case onames of
               SOME names => names
             | NONE =>
                 (Context.fresh (H, Variable.named "y"),
                  Context.fresh (H, Variable.named "z"))

        val fsTs = C.`> EQ $$ #[``y, ``f, Ts]
      in
        [ AUX |: H >> C.`> MEM $$ #[s, S]
        , MAIN |: H @@ (y, Ts) @@ (z, fsTs) >> P
        ] BY (fn [D, E] => D.`> FUN_ELIM $$ #[``f, s, D, y \\ (z \\ E)]
                | _ => raise Refine)
      end

    fun IsectMemberEq (oz, ok) (_ |: H >> P) =
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
        [ MAIN |: H' >> C.`> EQ $$ #[M,N, xP2 // ``z]
        , AUX |: H >> C.`> MEM $$ #[P1, C.`> (UNIV k) $$ #[]]
        ] BY (fn [D, E] => D.`> ISECT_MEMBER_EQ $$ #[z \\ D, E]
               | _ => raise Refine)
      end

    fun IsectMemberCaseEq (oisect, t) (_ |: H >> P) =
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
        [ MAIN |: H >> C.`> EQ $$ #[F1, F2, isect]
        , MAIN |: H >> C.`> MEM $$ #[t, S]
        ] BY mkEvidence ISECT_MEMBER_CASE_EQ
      end

    val SubsetEq = QuantifierEq (SUBSET, SUBSET_EQ)

    fun SubsetIntro (w, oz, ok) (_ |: H >> P) =
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
        [ AUX |: H >> C.`> MEM $$ #[ w, P1]
        , MAIN |: H >> xP2 // w
        , AUX |: H @@ (z, P1) >> C.`> MEM $$ #[xP2 // ``z, C.`> (UNIV k) $$ #[]]
        ] BY (fn [D, E, F] => D.`> SUBSET_INTRO $$ #[w, D, E, z \\ F]
               | _ => raise Refine)
      end

    fun IndependentSubsetIntro (_ |: H >> P) =
      let
        val #[P1, xP2] = P ^! SUBSET
        val (x, P2) = unbind xP2
        val _ = if hasFree (P2, x) then raise Refine else ()
      in
        [ MAIN |: H >> P1
        , MAIN |: H >> P2
        ] BY mkEvidence IND_SUBSET_INTRO
      end

    fun SubsetElim_ (z : Sequent.name, onames) (_ |: H >> P) =
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
        [ MAIN |: H' >> P'
        ] BY (fn [D] => D.`> SUBSET_ELIM $$ #[``z, s \\ (t \\ D)]
               | _ => raise Refine)
      end

    fun SubsetElim (hyp, onames) (goal as _ |: sequent) =
      SubsetElim_ (eliminationTarget hyp sequent, onames) goal

    fun SubsetMemberEq (oz, ok) (_ |: H >> P) =
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
        [ MAIN |: H >> C.`> EQ $$ #[s,t,S]
        , MAIN |: H >> xT // s
        , AUX |: H @@ (z,S) >> C.`> MEM $$ #[xT // ``z, C.`> (UNIV k) $$ #[]]
        ] BY (fn [D, E, F] => D.`> SUBSET_MEMBER_EQ $$ #[D, E, z \\ F]
               | _ => raise Refine)
      end

    fun NatEq (_ |: H >> P) =
      let
        val #[nat1, nat2, univ] = P ^! EQ
        val (UNIV _, _) = asApp univ
        val #[] = nat1 ^! NAT
        val #[] = nat2 ^! NAT
      in
        [] BY mkEvidence NAT_EQ
      end

    fun NatElim (hyp, onames) (_ |: H >> C) =
      let
        val z = eliminationTarget hyp (H >> C)
        val #[] = Context.lookup H z ^! NAT
        val (n,ih) =
          case onames of
               SOME names => names
             | NONE =>
                 (Context.fresh (H, Variable.named "n"),
                  Context.fresh (H, Variable.named "ih"))

        val zero = C.`> ZERO $$ #[]
        val succn = C.`> SUCC $$ #[``n]

        val J = Context.empty @@ (n, C.`> NAT $$ #[]) @@ (ih, subst (``n) z C)
        val H' = Context.mapAfter n (Syntax.subst succn z) (Context.interposeAfter H (z, J))
      in
        [ MAIN |: ctxSubst H zero z >> subst zero z C
        , MAIN |: H' >> subst succn z C
        ] BY (fn [D,E] => D.`> NAT_ELIM $$ #[``z, D, n \\ (ih \\ E)]
               | _ => raise Refine)
      end

    fun ZeroEq (_ |: H >> P) =
      let
        val #[zero1, zero2, nat] = P ^! EQ
        val #[] = nat ^! NAT
        val #[] = zero1 ^! ZERO
        val #[] = zero2 ^! ZERO
      in
        [] BY mkEvidence ZERO_EQ
      end

    fun SuccEq (_ |: H >> P) =
      let
        val #[succ1, succ2, nat] = P ^! EQ
        val #[] = nat ^! NAT
        val #[M] = succ1 ^! SUCC
        val #[N] = succ2 ^! SUCC
      in
        [ MAIN |: H >> C.`> EQ $$ #[M, N, C.`> NAT $$ #[]]
        ] BY mkEvidence SUCC_EQ
      end

    fun NatRecEq (ozC, onames) (_ |: H >> P) =
      let
        val #[rec1, rec2, A] = P ^! EQ
        val #[n, zero, succ] = rec1 ^! NATREC
        val #[n', zero', succ'] = rec2 ^! NATREC

        val zC =
          case ozC of
               SOME zC => unify (zC // n) A
             | NONE => Variable.named "z" \\ A

        val (npred, ih) =
            case onames of
                NONE =>
                (Context.fresh (H, Variable.named "n'"),
                 Context.fresh (H, Variable.named "ih"))
              | SOME names => names
        val H' = H @@ (npred, C.`> NAT $$ #[]) @@ (ih, zC // (`` npred))
        val succSubst = (succ // ``npred) // ``ih
        val succSubst' = (succ' // ``npred) // ``ih
      in
        [ MAIN |: H >> C.`>EQ $$ #[n, n', C.`> NAT $$ #[]]
        , MAIN |: H >> C.`>EQ $$ #[zero, zero', zC // (C.`> ZERO $$ #[])]
        , MAIN |: H' >> C.`>EQ $$ #[succSubst, succSubst', zC // (C.`> SUCC $$ #[`` npred])]
        ] BY (fn [N, D, E] => D.`> NATREC_EQ $$ #[N, D, npred \\ (ih \\ E)]
               | _ => raise Refine)
      end

    fun BaseEq (_ |: H >> P) =
      let
        val #[M, N, U] = P ^! EQ
        val #[] = M ^! BASE
        val #[] = N ^! BASE
        val (UNIV _, _) = asApp U
      in
        [] BY (fn [] => D.`> BASE_EQ $$ #[]
                | _ => raise Refine)
      end

    fun BaseIntro (_ |: H >> P) =
      let
        val #[] = P ^! BASE
      in
        [] BY (fn [] => D.`> BASE_INTRO $$ #[]
                | _ => raise Refine)
      end

    fun BaseMemberEq (_ |: H >> P) =
      let
        val #[M, N, U] = P ^! EQ
        val #[] = U ^! BASE
      in
        [ MAIN |: H >> C.`> CEQUAL $$ #[M, N]
        ] BY (fn [D] => D.`> BASE_MEMBER_EQ $$ #[D]
               | _ => raise Refine)
      end

    fun BaseElimEq (hyp, z) (_ |: H >> P) =
      let
        val eq = eliminationTarget hyp (H >> P)
        val #[M, N, U] = Context.lookup H eq ^! EQ
        val #[] = U ^! BASE
        val z =
            case z of
                SOME z => z
              | NONE => Context.fresh (H, Variable.named "H")
      in
        [ MAIN |: H @@ (z, C.`> CEQUAL $$ #[M, N]) >> P
        ] BY (fn [D] => D.`> BASE_ELIM_EQ $$ #[z \\ D]
               | _ => raise Refine)
      end

    fun ImageEq (_ |: H >> P) =
      let
        val #[M, N, U] = P ^! EQ
        val #[A1,f1] = M ^! IMAGE
        val #[A2,f2] = N ^! IMAGE
        val (UNIV _, _) = asApp U
      in
        [ MAIN |: H >> C.`> EQ $$ #[f1, f2, C.`> BASE $$ #[]]
        , MAIN |: H >> C.`> EQ $$ #[A1, A2, U]
        ] BY mkEvidence IMAGE_EQ
      end

    fun ImageMemEq (_ |: H >> P) =
      let
        val #[M, N, U] = P ^! EQ
        val #[f1,a1] = M ^! AP
        val #[f2,a2] = N ^! AP
        val #[A,f] = U ^! IMAGE
        val true = Syntax.eq (f,f1)
        val true = Syntax.eq (f,f2)
      in
        [ MAIN |: H >> C.`> EQ $$ #[a1, a2, A]
        , MAIN |: H >> C.`> EQ $$ #[f, f, C.`> BASE $$ #[]]
        ] BY mkEvidence IMAGE_MEM_EQ
      end

    fun ImageElim (hyp, ow) (_ |: H >> P) =
      let
        val z = eliminationTarget hyp (H >> P)
        val #[A,F] = Context.lookup H z ^! IMAGE
        val w =
         case ow of
             SOME w => w
           | NONE => Context.fresh (H, Variable.named "w")

        val K  = Context.insert Context.empty w Visibility.Hidden A
        val H1 = Context.interposeAfter H (z, K)

        val Fw = C.`> AP $$ #[F, ``w]
        val H2 = Context.mapAfter w (fn t => subst Fw z t) H1
        val P' = subst Fw z P
      in
        [ MAIN |: H2 >> P'
        ] BY (fn [D] => D.`> IMAGE_ELIM $$ #[w \\ D]
               | _ => raise Refine)
      end

    fun ImageEqInd (hyp, onames) (_ |: H >> P) =
      let
        val x = eliminationTarget hyp (H >> P)
        val #[T2',AP1,U] = Context.lookup H x ^! EQ
        val (a,b,y,z) =
          case onames of
               SOME names => names
             | NONE => (Context.fresh (H, Variable.named "a"),
             Context.fresh (H, Variable.named "b"),
             Context.fresh (H, Variable.named "y"),
             Context.fresh (H, Variable.named "z"))
        val #[A,f] = U ^! IMAGE
        val #[T2, AP2, T] = P ^! EQ
        val #[F,T1] = AP1 ^! AP
        val #[F',T1'] = AP2 ^! AP
        val true = Syntax.eq (T2,T2')
        val true = Syntax.eq (F,F')
        val true = Syntax.eq (T1,T1')
        val base = C.`> BASE $$ #[]
        val fa = C.`> AP $$ #[F,``a]
        val fb = C.`> AP $$ #[F,``b]
      in
        [ MAIN |: H >> C.`> EQ $$ #[F, F, base]
        , MAIN |: H >> C.`> EQ $$ #[T1, T1, A]
        , MAIN |: H >> C.`> EQ $$ #[AP1, AP1, T]
        , MAIN |: H @@ (a,base) @@ (b,base) @@ (y, C.`> EQ $$ #[fa,fa,T]) @@ (z, C.`> EQ $$ #[``a,``b,A]) >> C.`> EQ $$ #[fa,fb,T]
        ] BY (fn [D1,D2,D3,D4] => D.`> IMAGE_EQ_IND $$ #[D1,D2,D3, a \\ b \\ y \\ z \\ D4]
               | _ => raise Refine)
      end

    fun Witness M (_ |: H >> P) =
      let
        val M = Context.rebind H M
        val _ = assertClosed H M
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
        [ AUX |: H >> C.`> MEM $$ #[M, P]
        ] BY (fn [D] => D.`> WITNESS $$ #[M, D]
               | _ => raise Refine)
      end

    fun HypEq (_ |: H >> P) =
      let
        val P = P
        val #[M, M', A] = P ^! EQ
        val x = asVariable (unify M M')
        val _ = unify A (Context.lookup H x)
      in
        [] BY (fn _ => D.`> HYP_EQ $$ #[`` x])
      end

    val ProdEq = QuantifierEq (PROD, PROD_EQ)

    fun ProdIntro (w, oz, ok) (_ |: H >> P) =
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
        [ AUX |: H >> C.`> MEM $$ #[w, P1]
        , MAIN |: H >> xP2 // w
        , AUX |: H @@ (z, P1) >> C.`> MEM $$ #[xP2 // ``z, C.`> (UNIV k) $$ #[]]
        ] BY (fn [D, E, F] => D.`> PROD_INTRO $$ #[w, D, E, z \\ F]
               | _ => raise Refine)
      end

    fun IndependentProdIntro (_ |: H >> P) =
      let
        val #[P1, xP2] = P ^! PROD
        val (x, P2) = unbind xP2
        val _ = if hasFree (P2, x) then raise Refine else ()
      in
        [ MAIN |: H >> P1
        , MAIN |: H >> P2
        ] BY mkEvidence IND_PROD_INTRO
      end

    fun ProdElim (hyp, onames) (_ |: H >> P) =
      let
        val z = eliminationTarget hyp (H >> P)
        val #[S, xT] = Context.lookup H z ^! PROD
        val (s, t) =
          case onames of
               SOME names => names
             | NONE =>
                 (Context.fresh (H, Variable.named "s"),
                  Context.fresh (H, Variable.named "t"))

        val st = C.`> PAIR $$ #[``s, ``t]
        val J = Context.empty @@ (s, S) @@ (t, (xT // ``s))
        val H' = ctxSubst (Context.interposeAfter H (z, J)) st z
      in
        [ MAIN |: H' >> subst st z P
        ] BY (fn [D] => D.`> PROD_ELIM $$ #[``z, s \\ (t \\ D)]
               | _ => raise Refine)
      end

    fun PairEq (oz, ok) (_ |: H >> P) =
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
        [ MAIN |: H >> C.`> EQ $$ #[M, M', A]
        , MAIN |: H >> C.`> EQ $$ #[N, N', xB // M]
        , AUX |: H @@ (z,A) >> C.`> MEM $$ #[xB // `` z, C.`> (UNIV k) $$ #[]]
        ] BY (fn [D,E,F] => D.`> PAIR_EQ $$ #[D, E, z \\ F]
               | _ => raise Refine)
      end

    fun SpreadEq (ozC, oprod, onames) (_ |: H >> P) =
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
                     (inferType (H', C.`> SPREAD $$ #[``z, xyT1]))
                     (inferType (H', C.`> SPREAD $$ #[``z, uvT2]))
               in
                 z \\ Cz
               end
             | SOME zC => Context.rebind H zC

        val CE1' = unify CE1 (zC // E1)
        val Ts = xT // ``s
        val st = C.`> PAIR $$ #[``s, ``t]
        val E1pair = C.`> EQ $$ #[E1, st, prod]
        val Cst = zC // st
        val T1st = (xyT1 // ``s) // ``t
        val T2st = (uvT2 // ``s) // ``t
      in
        [ MAIN |: H >> C.`> EQ $$ #[E1, E2, prod]
        , MAIN |: H @@ (s, S) @@ (t, Ts) @@ (y, E1pair) >> C.`> EQ $$ #[T1st, T2st, Cst]
        ] BY (fn [D, E] => D.`> SPREAD_EQ $$ #[D, s \\ (t \\ (y \\ E))]
                | _ => raise Refine)
      end


    fun PlusEq (_ |: H >> P) =
      let
        val #[L, R, U] = P ^! EQ
        val (UNIV _, #[]) = asApp U
        val #[A, B] = L ^! PLUS
        val #[A', B'] = R ^! PLUS
      in
         [ MAIN |: H >> C.`> EQ $$ #[A, A', U]
         , MAIN |: H >> C.`> EQ $$ #[B, B', U]
         ] BY (fn [L, R] => D.`> PLUS_EQ $$ #[L, R]
                | _ => raise Refine)
      end

    fun PlusIntroL x (_ |: H >> P) =
      let
        val #[A, B] = P ^! PLUS
        val k = case x of SOME k => k | NONE => inferLevel (H, B)
      in
        [ MAIN |: H >> A
        , AUX |: H >> C.`> MEM $$ #[B, C.`> (UNIV k) $$ #[]]
        ] BY (fn [InA, WfB] => D.`> PLUS_INTROL $$ #[InA, WfB]
               | _ => raise Refine)
      end

    fun PlusIntroR x (_ |: H >> P) =
      let
        val #[A, B] = P ^! PLUS
        val k = case x of SOME k => k | NONE => inferLevel (H, A)
      in
        [ MAIN |: H >> B
        , AUX |: H >> C.`> MEM $$ #[A, C.`> (UNIV k) $$ #[]]
        ] BY (fn [InB, WfA] => D.`> PLUS_INTROR $$ #[InB, WfA]
               | _ => raise Refine)
      end

    fun PlusElim (i, onames) (_ |: H >> P) =
      let
        val z = eliminationTarget i (H >> P)
        val #[A, B] = Context.lookup H z ^! PLUS
        val (s, t) =
            case onames of
                SOME names => names
              | NONE => (Context.fresh (H, Variable.named "s"),
                         Context.fresh (H, Variable.named "t"))
        val withs = C.`> INL $$ #[``s]
        val witht = C.`> INR $$ #[``t]
        val H's = ctxSubst (Context.interposeAfter H (z, Context.empty @@ (s, A)))
                           withs z
        val H't = ctxSubst (Context.interposeAfter H (z, Context.empty @@ (t, B)))
                           witht z
      in
        [ MAIN |: H's >> subst withs z P
        , MAIN |: H't >> subst witht z P
        ] BY (fn [L, R] => D.`> PLUS_ELIM $$ #[``z, s \\ L, t \\ R]
               | _ => raise Refine)
      end

    fun InlEq x (_ |: H >> P) =
      let
        val #[M, N, T] = P ^! EQ
        val #[A, B] = T ^! PLUS
        val #[M'] = M ^! INL
        val #[N'] = N ^! INL
        val k = case x of SOME k => k | NONE => inferLevel (H, B)
      in
        [ MAIN |: H >> C.`> EQ $$ #[M', N', A]
        , AUX |: H >> C.`> MEM $$ #[B, C.`> (UNIV k) $$ #[]]
        ] BY (fn [In, Wf] => D.`> INL_EQ $$ #[In, Wf]
               | _ => raise Refine)
      end

    fun InrEq x (_ |: H >> P) =
      let
        val #[M, N, T] = P ^! EQ
        val #[A, B] = T ^! PLUS
        val #[M'] = M ^! INR
        val #[N'] = N ^! INR
        val k = case x of SOME k => k | NONE => inferLevel (H, A)
      in
        [ MAIN |: H >> C.`> EQ $$ #[M', N', B]
        , AUX |: H >> C.`> MEM $$ #[A, C.`> (UNIV k) $$ #[]]
        ] BY (fn [In, Wf] => D.`> INR_EQ $$ #[In, Wf]
               | _ => raise Refine)
      end

    fun DecideEq C (A, B, x) (_ |: H >> P) =
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
                    @@ (eq, C.`> EQ $$ #[M', C.`> INL $$ #[``s], C.`> PLUS $$ #[A, B]])
        val H't = H @@ (t, B)
                    @@ (eq, C.`> EQ $$ #[M', C.`> INR $$ #[``t], C.`> PLUS $$ #[A, B]])
        val C's = subst1 C (C.`> INL $$ #[``s])
        val C't = subst1 C (C.`> INR $$ #[``t])
      in
        [ MAIN |: H >> C.`> EQ $$ #[M', N', C.`> PLUS $$ #[A, B]]
        , MAIN |: H's >> C.`> EQ $$ #[subst1 sL (``s), subst1 sL' (``s), C's]
        , MAIN |: H't >> C.`> EQ $$ #[subst1 tR (``t), subst1 tR' (``t), C't]
        ] BY (fn [EqM, EqL, EqR] =>
                 D.`> DECIDE_EQ $$ #[EqM, eq \\ (s \\ EqR), eq \\ (t \\ EqL)]
               | _ => raise Refine)
      end

    fun AtomEq (_ |: H >> P) =
      let
        val #[atm, atm', uni] = P ^! EQ
        val #[] = atm ^! ATOM
        val #[] = atm' ^! ATOM
        val (UNIV _, _) = asApp uni
      in
        [] BY mkEvidence ATOM_EQ
      end

    fun TokenEq (_ |: H >> P) =
      let
        val #[tok, tok', atm] = P ^! EQ
        val #[] = atm ^! ATOM
        val (TOKEN s1, _) = asApp tok
        val (TOKEN s2, _) = asApp tok'
        val true = s1 = s2
      in
        [] BY mkEvidence TOKEN_EQ
      end


  fun TestAtomEq oz (_ |: H >> P) =
    let
      val #[match1, match2, T] = P ^! EQ
      val #[u1, v1, s1, t1] = match1 ^! TEST_ATOM
      val #[u2, v2, s2, t2] = match2 ^! TEST_ATOM
      val z = Context.fresh (H, case oz of NONE => Variable.named "z" | SOME z => z)
      val atm = C.`> ATOM $$ #[]
      val u1v1 = C.`> EQ $$ #[u1, v1, atm]
      val u1v1' = C.`> NOT $$ #[u1v1]
    in
      [ MAIN |: H >> C.`> EQ $$ #[u1, u2, atm]
      , MAIN |: H >> C.`> EQ $$ #[v1, v2, atm]
      , MAIN |: H @@ (z, u1v1) >> C.`> EQ $$ #[s1, s2, T]
      , MAIN |: H @@ (z, u1v1') >> C.`> EQ $$ #[t1, t2, T]
      ] BY (fn [D,E,F,G] => D.`> TEST_ATOM_EQ $$ #[D,E,z \\ F, z \\ G]
             | _ => raise Refine)
    end

  fun TestAtomReduceLeft (_ |: H >> P) =
    let
      val #[test, t2, T] = P ^! EQ
      val #[u,v,s,t] = test ^! TEST_ATOM
    in
      [ MAIN |: H >> C.`> EQ $$ #[s, t2, T]
      , AUX |: H >> C.`> EQ $$ #[u, v, C.`> ATOM $$ #[]]
      ] BY mkEvidence TEST_ATOM_REDUCE_LEFT
    end

  fun TestAtomReduceRight (_ |: H >> P) =
    let
      val #[test, t2, T] = P ^! EQ
      val #[u,v,s,t] = test ^! TEST_ATOM
    in
      [ MAIN |: H >> C.`> EQ $$ #[t, t2, T]
      , AUX |: H >> C.`> NOT $$ #[C.`> EQ $$ #[u, v, C.`> ATOM $$ #[]]]
      ] BY mkEvidence TEST_ATOM_REDUCE_RIGHT
    end

   fun MatchTokenEq (_ |: H >> P) =
     let
       val #[match1, match2, C] = P ^! EQ
       val (MATCH_TOKEN toks1, subterms1) = asApp match1
       val (MATCH_TOKEN toks2, subterms2) = asApp match2
       val target1 = Vector.sub (subterms1, 0)
       val target2 = Vector.sub (subterms2, 0)
       fun branches (toks, subterms)=
         Vector.foldri
           (fn (i, tok, dict) =>
             StringListDict.insert dict tok (Vector.sub (subterms, i + 1)))
           StringListDict.empty
           toks

       fun subdomain (keys, dict) = Vector.all (StringListDict.member dict) keys
       val branches1 = branches (toks1, subterms1)
       val branches2 = branches (toks2, subterms2)
       val catchAll1 = Vector.sub (subterms1, Vector.length subterms1 - 1)
       val catchAll2 = Vector.sub (subterms2, Vector.length subterms2 - 1)

       val true =
         subdomain (toks1, branches2)
           andalso subdomain (toks2, branches1)

       val x = Context.fresh (H, Variable.named "x")
       val y = Context.fresh (H, Variable.named "y")

       fun tokToGoal tok =
         let
           val X = C.`> CEQUAL $$ #[target1, C.`> (TOKEN tok) $$ #[]]
           val Y = C.`> CEQUAL $$ #[target2, C.`> (TOKEN tok) $$ #[]]
           val H' = H @@ (x, X) @@ (y, Y)
         in
           MAIN |: H' >> C.`> EQ $$ #[StringListDict.lookup branches1 tok, StringListDict.lookup branches2 tok, C]
         end

       val positiveGoals =
         List.tabulate
           (Vector.length toks1,
            fn i => tokToGoal (Vector.sub (toks1, i)))

       val catchAllGoal =
         let
           val X = C.`> CEQUAL $$ #[match1, catchAll1]
           val Y = C.`> CEQUAL $$ #[match2, catchAll2]
           val H' = H @@ (x, X) @@ (y, Y)
         in
           MAIN |: H' >> C.`> EQ $$ #[catchAll1, catchAll2, C]
         end

       val subgoals =
         (MAIN |: H >> C.`> EQ $$ #[target1, target2, C.`> ATOM $$ #[]])
           :: positiveGoals
            @ [catchAllGoal]
     in
       subgoals BY (fn Ds =>
         D.`> (MATCH_TOKEN_EQ toks1) $$
           Vector.tabulate
             (List.length Ds, fn i =>
                if i = 0 then
                  List.nth (Ds, i)
                else
                  x \\ (y \\ List.nth (Ds, i))))
     end

    fun Hypothesis_ x (_ |: H >> P) =
      let
        val (P', visibility) = Context.lookupVisibility H x
        val P'' = unify P P'
      in
        (case visibility of
             Visibility.Visible => ()
           | Visibility.Hidden => assertIrrelevant (H, P''));
        [] BY (fn _ => ``x)
      end

    fun Hypothesis hyp (goal as _ |: S) = Hypothesis_ (eliminationTarget hyp S) goal

    fun Assumption (goal as _ |: H >> P) =
      case Context.search H (fn x => Syntax.eq (P, x)) of
           SOME (x, _) => Hypothesis_ x goal
         | NONE => raise Refine

    fun Assert (term, name) (_ |: H >> P) =
      let
        val z =
            case name of
                SOME z => z
              | NONE => Context.fresh (H, Variable.named "H")
        val term' = Context.rebind H term
      in
        [ AUX |: H >> term'
        , MAIN |: H @@ (z, term') >> P
        ] BY (fn [D, E] => subst D z E
               | _ => raise Refine)
      end

    structure LevelSolver = LevelSolver (SyntaxWithUniverses (Syntax))

    structure SequentLevelSolver = SequentLevelSolver
      (structure Solver = LevelSolver
       structure Abt = Syntax
       structure Sequent = Sequent)

    local
      open Conversionals
      infix CTHEN

      fun convTheorem theta world =
        let
          val extract = Development.lookupExtract world theta
        in
          fn M =>
            case out M of
               theta' $ #[] =>
                 if Syntax.Operator.eq (theta, theta') then
                   extract
                 else
                   raise Conv.Conv
             | _ => raise Conv.Conv
        end

      fun convOperator theta world =
        Development.lookupDefinition world theta
          handle Subscript => convTheorem theta world
    in
      fun Unfolds (world, thetas) (lbl |: H >> P) =
        let
          val conv =
            foldl (fn ((theta, ok), acc) =>
              let
                val k = case ok of SOME k => k | NONE => Level.base
                val conv =
                  LevelSolver.subst (LevelSolver.Level.yank k)
                    o CDEEP (convOperator theta world)
              in
                acc CTHEN conv
              end) CID thetas

        in
          [ lbl |: Context.map conv H >> conv P
          ] BY (fn [D] => D
                 | _ => raise Refine)
        end
    end

      fun Lemma (world, theta) (_ |: H >> P) =
        let
          val {statement, evidence} = Development.lookupTheorem world theta
          val constraints = SequentLevelSolver.generateConstraints (statement, H >> P)
          val substitution = LevelSolver.Level.resolve constraints
          val shovedEvidence = LevelSolver.subst substitution (Susp.force evidence)
          val lemmaOperator = LEMMA {label = Operator.toString theta}
        in
          [] BY (fn _ => D.`> lemmaOperator $$ #[])
        end

      fun Fiat (_ |: H >> P) =
        [] BY (fn _ => D.`> FIAT $$ #[])

      fun RewriteGoal (c : conv) (_ |: H >> P) =
        [ MAIN |: Context.map c H >> c P
        ] BY (fn [D] => D | _ => raise Refine)

      fun EqSym (_ |: H >> P) =
        let
          val #[M,N,A] = P ^! EQ
        in
          [ MAIN |: H >> C.`> EQ $$ #[N,M,A]
          ] BY mkEvidence EQ_SYM
        end


      structure Meta = MetaAbt(Syntax)
      structure MetaAbt = AbtUtil(Meta.Meta)
      structure Unify = AbtUnifyOperators
        (structure A = MetaAbt
         structure O = Meta.MetaOperator)

      fun applySolution sol e =
        Meta.unconvert (fn _ => raise Fail "Impossible")
          (Unify.Solution.foldl
            (fn (v, e', e) => MetaAbt.substOperator (fn _ => e') (Meta.MetaOperator.META v) e)
            e
            sol)

      fun EqSubst (eq, xC, ok) (_ |: H >> P) =
        let
          val #[M,N,A] = Context.rebind H eq ^! EQ
          val xC = Context.rebind H xC

          val fvs = List.map #1 (Context.listItems H)
          val meta = Meta.convertFree fvs (xC // M)
          val solution = Unify.unify (Meta.convertFree fvs (xC // M), Meta.convert P)
          val xC = applySolution solution (Meta.convertFree fvs xC)

          val (H', x, C) = ctxUnbind (H, A, xC)
          val k = case ok of SOME k => k | NONE => inferLevel (H', C)
        in
          [ AUX |: H >> eq
          , MAIN |: H >> xC // N
          , AUX |: H' >> C.`> MEM $$ #[C, C.`> (UNIV k) $$ #[]]
          ] BY (fn [D,E,F] => D.`> EQ_SUBST $$ #[D, E, x \\ F]
                 | _ => raise Refine)
      end

    fun Thin hyp (_ |: H >> P) =
      let
        val z = eliminationTarget hyp (H >> P)
        val H' = Context.thin H z
      in
        [ MAIN |: H' >> P
        ] BY (fn [D] => D | _ => raise Refine)
      end

    local
      structure Tacticals = Tacticals (Lcf)
      open Tacticals
      infix THEN THENL
    in
      datatype ForallType = ForallIsect | ForallFun

      local
        open CttCalculusView
      in
        fun stripForalls (H, P) =
          case project P of
               ISECT $ #[A, xB] =>
                 let
                   val (H', x, B) = ctxUnbind (H, A, xB)
                   val (xs, Q) = stripForalls (H', B)
                 in
                   (xs @ [(ForallIsect, x)], Q)
                 end
             | FUN $ #[A, xB] =>
                 let
                   val (H', x, B) = ctxUnbind (H, A, xB)
                   val (xs, Q) = stripForalls (H', B)
                 in
                   (xs @ [(ForallFun, x)], Q)
                 end
             | _ => ([], P)
      end

      fun BHyp hyp (goal as _ |: (sequent as H >> P)) =
        let
          val target = eliminationTarget hyp sequent

          val (variables, Q) = stripForalls (H, Context.lookup H target)
          val fvs = List.map #1 (Context.listItems H)
          val solution = Unify.unify (Meta.convertFree fvs Q, Meta.convertFree fvs P)

          val instantiations = List.map (fn (ty, v) => (ty, Unify.Solution.lookup solution v)) variables

          val targetRef = ref target
          fun go [] = ID
            | go ((ty, e) :: es) = fn goal' as _ |: H' >> _ =>
              let
                val currentTarget = Context.rebindName H' (! targetRef)
                val nextTarget = Variable.prime currentTarget
                val _ = targetRef := nextTarget
                val instantiation = Meta.unconvert (fn _ => raise Refine) e
                val eqName = Context.fresh (H', Variable.named "_")
                val names = (nextTarget, eqName)
                val hyp = HypSyn.NAME currentTarget
                val elim =
                  case ty of
                       ForallIsect => IsectElim
                     | ForallFun => FunElim
                val tac =
                  elim (hyp, instantiation, SOME names)
                    THEN Thin hyp
              in
                (tac THENL [ID, go es]) goal'
              end
        in
          go (rev instantiations) goal
        end


      fun HypEqSubst (dir, hyp, xC, ok) (goal as _ |: H >> P) =
        let
          val z = eliminationTarget hyp (H >> P)
          val X = Context.lookup H z
        in
          case dir of
               Dir.RIGHT => (EqSubst (X, xC, ok) THENL [Hypothesis_ z, ID, ID]) goal
             | Dir.LEFT =>
                 let
                   val #[M,N,A] = X ^! EQ
                 in
                   (EqSubst (C.`> EQ $$ #[N,M,A], xC, ok)
                     THENL [EqSym THEN Hypothesis_ z, ID, ID]) goal
                 end
        end

      fun CEqEq (_ |: H >> P) =
        let
          val #[M, N, U] = P ^! EQ
          val (UNIV _, _) = asApp U
          val #[L, R] = M ^! CEQUAL
          val #[L', R'] = N ^! CEQUAL
        in
          [ MAIN |: H >> C.`> CEQUAL $$ #[L, L']
          , MAIN |: H >> C.`> CEQUAL $$ #[R, R']
          ] BY (fn [D, E] => D.`> CEQUAL_EQ $$ #[D, E]
                 | _ => raise Refine)
        end

      fun CEqMemEq (_ |: H >> P) =
        let
          val #[M, N, E] = P ^! EQ
          val #[] = M ^! AX
          val #[] = N ^! AX
          val #[_, _] = E ^! CEQUAL
        in
          [ MAIN |: H >> E
          ] BY mkEvidence CEQUAL_MEMBER_EQ
        end

      fun ApproxEq (_ |: H >> P) =
        let
          val #[approx1, approx2, univ] = P ^! EQ
          val (UNIV _, _) = asApp univ
          val #[M,N] = approx1 ^! APPROX
          val #[M',N'] = approx2 ^! APPROX
          val base = C.`> BASE $$ #[]
        in
          [ MAIN |: H >> C.`> EQ $$ #[M,M',base]
          , MAIN |: H >> C.`> EQ $$ #[N,N',base]
          ] BY mkEvidence APPROX_EQ
        end

      fun ApproxMemEq (_ |: H >> P) =
        let
          val #[M, N, E] = P ^! EQ
          val #[] = M ^! AX
          val #[] = N ^! AX
          val #[_, _] = E ^! APPROX
        in
          [ MAIN |: H >> E
          ] BY mkEvidence APPROX_MEMBER_EQ
        end

      fun ApproxExtEq (_ |: H >> P) =
        let
          val #[approx1, approx2, univ] = P ^! EQ
          val (UNIV _, _) = asApp univ
          val #[_,_] = approx1 ^! APPROX
          val #[_,_] = approx2 ^! APPROX
          val iff = C.`> IFF $$ #[approx1, approx2]
          val squ = C.`> SQUASH $$ #[iff]
        in
          [ MAIN |: H >> squ
          ] BY mkEvidence APPROX_EXT_EQ
        end

      local
        fun bothStuck M N =
          (Semantics.step M; raise Refine)
          handle Semantics.Stuck _ =>
            (Semantics.step N; raise Refine)
               handle Semantics.Stuck _ => ()
      in
        fun ApproxRefl (_ |: H >> P) =
          let
            val #[M, N] = P ^! APPROX
            val () = (unify M N; ()) handle Refine => bothStuck M N
          in
            [] BY mkEvidence APPROX_REFL
          end
      end

      fun ApproxElim hyp (goal as _ |: (sequent as H >> P)) =
        let
          val z = eliminationTarget hyp sequent
          val _ = Context.lookup H z ^! APPROX
          val ax = C.`> AX $$ #[]
          val H' = ctxSubst H ax z
          val P' = subst ax z P
        in
          [ MAIN |: H' >> P'
          ] BY (fn [D] => D.`> APPROX_ELIM $$ #[`` z, D]
                 | _ => raise Refine)
        end

      fun CEqSym (_ |: H >> P) =
        let
          val #[M, N] = P ^! CEQUAL
        in
          [ MAIN |: H >> C.`> CEQUAL $$ #[N, M]
          ] BY (fn [D] => D.`> CEQUAL_SYM $$ #[D]
                 | _ => raise Refine)
        end

      fun CEqStep (_ |: H >> P) =
        let
          val #[M, N] = P ^! CEQUAL
          val M' =
              case Semantics.step M handle Semantics.Stuck _ => raise Refine of
                  Semantics.STEP M' => M'
                | Semantics.CANON => raise Refine
                | Semantics.NEUTRAL => raise Refine
        in
          [ MAIN |: H >> C.`> CEQUAL $$ #[M', N]
          ] BY (fn [D] => D.`> CEQUAL_STEP $$ #[D]
                 | _ => raise Refine)
        end

      fun CEqSubst (eq, xC) (_ |: H >> P) =
        let
          val eq = Context.rebind H eq
          val #[M, N] = eq ^! CEQUAL

          val fvs = List.map #1 (Context.listItems H)
          val meta = Meta.convertFree fvs (xC // M)
          val solution = Unify.unify (Meta.convertFree fvs (xC // M), Meta.convert P)
          val xC = applySolution solution (Meta.convertFree fvs xC)

          val _ = unify P (xC // M)
        in
          [ AUX |: H >> eq
          , MAIN |: H >> xC // N
          ] BY (fn [D, E] => D.`> CEQUAL_SUBST $$ #[D, E]
                 | _ => raise Refine)
        end

      fun HypCEqSubst (dir, hyp, xC) (goal as _ |: H >> P) =
        let
          val z = eliminationTarget hyp (H >> P)
          val X = Context.lookup H z
        in
          case dir of
              Dir.RIGHT =>
              (CEqSubst (X, xC) THENL [Hypothesis_ z, ID]) goal
            | Dir.LEFT =>
              let
                val #[M,N] = X ^! CEQUAL
              in
                (CEqSubst (C.`> CEQUAL $$ #[N,M], xC)
                          THENL [CEqSym THEN Hypothesis_ z, ID]) goal
              end
        end

      fun CEqApprox (_ |: H >> P) =
        let
          val #[M, N] = P ^! CEQUAL
        in
          [ MAIN |: H >> C.`> APPROX $$ #[M, N]
          , MAIN |: H >> C.`> APPROX $$ #[N, M]
          ] BY mkEvidence CEQUAL_APPROX
        end

      fun AssumeHasValue (onames, ok) (_ |: H >> P) =
        let
          val #[M,N] = P ^! APPROX
          val y =
            case onames of
                 SOME names => names
               | NONE => Context.fresh (H, Variable.named "y")
          val hv = C.`> HASVALUE $$ #[M]
          val k = case ok of SOME k => k | NONE => inferLevel (H, hv)
          val uni = C.`> (UNIV k) $$ #[]
          val mem = C.`> MEM $$ #[hv, uni]
        in
          [ MAIN |: H @@ (y, hv) >> P
          , AUX |: H >> mem
          ] BY (fn [A,B] => D.`> ASSUME_HAS_VALUE $$ #[y \\ A,B]
                 | _ => raise Refine)
        end

      fun BottomDiverges hyp (_ |: H >> P) =
        let
          val x = eliminationTarget hyp (H >> P)
          val h = Context.lookup H x
          val #[M] = h ^! HASVALUE
          val #[] = M ^! BOT
        in
          [] BY (fn _ => D.`> BOTTOM_DIVERGES $$ #[``x])
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
              newSubGoal (H @@ (x, C.`> BASE $$ #[]))
                         (x :: vs)
                         (t1', subst (``x) y t2')
            | (_, _) =>
              (List.rev vs, MAIN |: H >> C.`> CEQUAL $$ #[t1, t2])

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
        fun CEqStruct (_ |: H >> P) =
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
                            D.`> (CEQUAL_STRUCT (Vector.map List.length boundVars))
                              $$ bindVars boundVars (Vector.fromList Ds)
                            handle _ => raise Refine)
          end
        end
    end

    local
      structure Tacticals = Tacticals(Lcf)
      open Tacticals CttCalculusView infix THEN
    in
      fun EqInSupertype (goal as _ |: H >> P) =
        let
          val #[M,N,A] = P ^! EQ
          val result =
            Context.search H (fn A' =>
              case project A' of
                   SUBSET $ #[A'', _] => Syntax.eq (A, A'')
                 | _ => false)
          val x = case result of SOME (x,_) => x | NONE => raise Refine
        in
          (SubsetElim_ (x, NONE) THEN HypEq) goal
        end
    end

    local
      structure Unify = UnifySequent(Sequent)
    in
      fun MatchSingle (hyps, goal, body) (l |: H >> P) =
        let
          val {matched, subst} =
            Unify.unify ({hyps = hyps, goal = goal}, (H >> P))
              handle Unify.Mismatch => raise Refine
        in
          body subst (l |: H >> P)
        end
    end

  end

  structure Conversions =
  struct
    open Conversionals Conv

    val Step : conv = fn M =>
      case Semantics.step M of
           Semantics.STEP M' => M'
         | _ => raise Conv
  end
end

structure Refiner = Refiner
  (structure Lcf = Lcf
   structure Syntax = Syntax
   structure Conv = Conv
   structure Semantics = Semantics
   structure Sequent = Sequent
   structure Development = Development
   structure Builtins = Builtins)
