functor UtilityRules
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
   sharing type Development.term = Syntax.t

   exception Refine) =
struct
  open Context
  open Syntax
  open Operator OperatorType
  infix $ \
  infix 8 $$ // \\

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

  fun @@ (H, (x,A)) = Context.insert H x Visibility.Visible A

  fun asApp M =
    case out M of
         O $ ES => (O, ES)
       | _ => raise Refine

  fun ^! (M, O) =
    case out M of
         O' $ ES => if Operator.eq (O, O') then ES else raise Refine
       | _ => raise Refine

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

  fun eliminationTarget i (H >> P) =
    let
      val z = Context.nth H (i - 1)
      val (A, visibility) = Context.lookupVisibility H z
    in
      case visibility of
           Visibility.Hidden =>
            (assertIrrelevant (H, P); z)
         | Visibility.Visible => z
    end

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
end
