(* Note, here : vs :> is very much necessary. It avoids
 * us having to write a [sharing] clause for everything
 * included in RULES_UTIL_INPUT.
 *)
functor RulesUtil(M : RULES_UTIL_INPUT) : RULES_UTIL =
struct
  open M
  open Syntax CttCalculus Derivation
  open Goal Sequent
  infix 3 >>
  infix 2 |:

  infix $ \
  infix 8 $$ //
  infixr 8 \\

  type tactic = Lcf.tactic
  type conv = Conv.conv
  type name = Sequent.name
  type term = Syntax.t
  type goal = Sequent.sequent

  type operator = Syntax.Operator.t
  type hyp = name HypSyn.t
  type world = Development.world

  structure CttCalculusView = RestrictAbtView
    (structure Abt = Syntax
     structure Injection = CttCalculusInj)

  structure Conversionals = Conversionals
    (structure Syntax = Syntax
     structure Conv = Conv)

  structure C = CttCalculusInj
  structure D = DerivationInj

  structure Meta = MetaAbt(Syntax)
  structure MetaAbt = AbtUtil(Meta.Meta)
  structure Unify = AbtUnifyOperators
    (structure A = MetaAbt
     structure O = Meta.MetaOperator)

  fun applySolution sol (P, e) =
    let
      val e =
        Unify.Solution.foldl
          (fn (v, e', e) => MetaAbt.substOperator (fn _ => e') (Meta.MetaOperator.META v) e)
          e
          sol
      fun go (MetaAbt.` v, _) = `` v
        | go (MetaAbt.\ (v, M), v' \ M') =
          v \\ go (MetaAbt.out M, out (subst (`` v) v' M'))
        | go (MetaAbt.$ (Meta.MetaOperator.WILD, _), M') = into M'
        | go (MetaAbt.$ (Meta.MetaOperator.META v, _), _) = `` v
        | go (MetaAbt.$ (Meta.MetaOperator.NORMAL oper, args), _ $ args') =
          oper $$ Vector.map go
            (VectorPair.zip (Vector.map MetaAbt.out args, Vector.map out args'))
        | go (M, _) =
          Meta.unconvert
            (fn _ => raise Fail "applySolution failed")
            (MetaAbt.into M)
    in
      go (MetaAbt.out e, out P)
    end

  fun convertToPattern (H, e) =
    let
      open Meta
      val fvs = List.map #1 (Context.listItems H)
      val wildVars =
        List.filter (fn v => "_" = Variable.toString v)
                    (freeVariables e)
      val meta = convertFree fvs e
      val wild = MetaAbt.into (MetaAbt.$ (MetaOperator.WILD, #[]))
    in
      List.foldl
        (fn (v, t) => MetaAbt.substOperator (fn _ => wild) (MetaOperator.META v) t)
        meta
        wildVars
    end

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
            (assertIrrelevant (H, P) handle _ => assertIrrelevant (H, A); z)
         | Visibility.Visible => z
    end

  local
    open CttCalculusView
  in
    fun inferLevel (H, P) =
      case project P of
           UNIV l $ _ => Level.succ l
         | CONTAINER i $ #[] => Level.succ i
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
end
