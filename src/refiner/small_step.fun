functor SmallStepUtil (S : SMALL_STEP) : SMALL_STEP_UTIL =
struct
  open S
  type petrol = int

  local
    val guzzle = Option.map (fn x => x - 1)
    fun expended (SOME x) = x <= 0
      | expended NONE = false

    fun go (M, gas) i =
      if expended gas then
        (M,i)
      else
        case step M of
             STEP M' => go (M', guzzle gas) (i + 1)
           | CANON => (M,i)
           | NEUTRAL => (M,i)
  in
    fun steps (M, gas) = go (M, gas) 0
  end
end

functor SmallStep (Syn : ABT_UTIL where type Operator.t = UniversalOperator.t)
        : SMALL_STEP where type syn = Syn.t =
struct
  type syn = Syn.t

  open Syn
  open Operator CttCalculus CttCalculusInj
  structure View = RestrictAbtView (structure Abt = Syn and Injection = CttCalculusInj)
  open View

  infix 8 $ $$ //
  infixr 7 \ \\

  fun theta $$ es =
    Syn.$$ (`> theta, es)

  exception Stuck of Syn.t
  datatype t = STEP of Syn.t | CANON | NEUTRAL

  fun stepSpreadBeta (P, E) =
    case project P of
        PAIR $ #[L, R] => (E // L) // R
      | _ => raise Stuck (SPREAD $$ #[P, E])

  fun stepDomBeta F =
    case project F of
        MAKE_CONTAINER $ #[dom, xProj] => dom
      | EXTEND $ #[dom, xProj] => dom
      | _ => raise Stuck (DOM $$ #[F])

  fun stepProjBeta (F, d) =
    case project F of
        MAKE_CONTAINER $ #[dom, xProj] => xProj // d
      | EXTEND $ #[dom, xProj] => xProj // d
      | _ => raise Stuck (PROJ $$ #[F, d])

  fun stepRefinementBeta (F, u) =
    case project u of
        NEIGH_NIL $ #[] => UNIT $$ #[]
      | EXTEND $ #[v, pE] =>
          let
            val s = Variable.named "s"
          in
            PROD $$ #[REFINEMENT $$ #[F, v], s \\ PROJ $$ #[F, pE // ``s]]
          end
      | _ => raise Stuck (REFINEMENT $$ #[F, u])

  fun stepApBeta (F, A) =
    case project F of
        LAM $ #[B] => B // A
      | _ => raise Stuck (AP $$ #[F, A])

  fun stepDecideBeta (S, L, R) =
    case project S of
        INL $ #[A] => L // A
      | INR $ #[B] => R // B
      | _ => raise Stuck (DECIDE $$ #[S, L, R])

  fun stepNatrecBeta (M, Z, xyS) =
    case project M of
         ZERO $ #[] => Z
       | SUCC $ #[N] => (xyS // N) // (NATREC $$ #[N, Z, xyS])
       | _ => raise Stuck (NATREC $$ #[M, Z, xyS])

  fun stepNeighIndBeta (M, Z, xypS) =
    case project M of
         NEIGH_NIL $ #[] => Z
       | EXTEND $ #[U, rE] =>
           let
           in
             xypS // U // (LAM $$ #[rE]) // (NEIGH_IND $$ #[U, Z, xypS])
           end
       | _ => raise Stuck (NEIGH_IND $$ #[M, Z, xypS])

  fun stepWTreeRecBeta (M, xyzD) =
    case project M of
         SUP $ #[extend] =>
         let
           val v = Variable.named "v"
           val S = DOM $$ #[extend]
         in
           xyzD // S // (LAM $$ #[v \\ (PROJ $$ #[extend, ``v])]) // (LAM $$ #[v \\ WTREE_REC $$ #[PROJ $$ #[extend, ``v], xyzD]])
         end
       | _ => raise Stuck (WTREE_REC $$ #[M, xyzD])

  fun stepFix (F) = AP $$ #[F, FIX $$ #[F]]

  fun stepCbv (A, F) = F // A

  fun stepMatchTokenBeta e (M, branches, catchAll) =
    case project M of
         TOKEN tok $ #[] => (StringListDict.lookup branches tok handle _ => catchAll)
       | _ => raise Stuck e

  fun stepTestAtomBeta (U, V, S, T) =
    case (project U, project V) of
         (TOKEN u $ #[], TOKEN v $ #[]) => if u = v then S else T
       | _ => raise Stuck (TEST_ATOM $$ #[U, V, S, T])

  fun step' e =
    case project e of
        UNIV _ $ _ => CANON
      | VOID $ _ => CANON
      | UNIT $ _ => CANON
      | AX $ _ => CANON
      | PROD $ _ => CANON
      | PAIR $ _ => CANON
      | FUN $ _ => CANON
      | LAM $ _ => CANON
      | ISECT $ _ => CANON
      | EQ $ _ => CANON
      | MEM $ _ => CANON
      | SUBSET $ _ => CANON
      | PLUS $ _ => CANON
      | INL $ _ => CANON
      | INR $ _ => CANON
      | NAT $ _ => CANON
      | ZERO $ _ => CANON
      | SUCC $ _ => CANON
      | IMAGE $ _ => CANON
      | BASE $ _ => CANON
      | TOKEN _ $ _ => CANON
      | APPROX $ _ => CANON
      | CEQUAL $ _ => CANON
      | WTREE $ _ => CANON
      | SUP $ _ => CANON
      | CONTAINER _ $ _ => CANON
      | MAKE_CONTAINER $ _ => CANON
      | EXTEND $ _ => CANON
      | NEIGH_NIL $ _ => CANON
      | NEIGH $ _ => CANON
      | AP $ #[L, R] =>
          (case step L of
              STEP L' => STEP (AP $$ #[L', R])
            | CANON => STEP (stepApBeta (L, R))
            | NEUTRAL => NEUTRAL)
      | SPREAD $ #[P, E] =>
          (case step P of
              STEP P' => STEP (SPREAD $$ #[P', E])
            | CANON => STEP (stepSpreadBeta (P, E))
            | NEUTRAL => NEUTRAL)
      | DOM $ #[F] =>
          (case step F of
              STEP F' => STEP (DOM $$ #[F'])
            | CANON => STEP (stepDomBeta F)
            | NEUTRAL => NEUTRAL)
      | PROJ $ #[F, d] =>
          (case step F of
              STEP F' => STEP (PROJ $$ #[F', d])
            | CANON => STEP (stepProjBeta (F, d))
            | NEUTRAL => NEUTRAL)
      | REFINEMENT $ #[F, u] =>
          (case step u of
              STEP u' => STEP (REFINEMENT $$ #[F, u'])
            | CANON => STEP (stepRefinementBeta (F, u))
            | NEUTRAL => NEUTRAL)
      | FIX $ #[F] =>
          (case step F of
              STEP F' => STEP (FIX $$ #[F'])
            | CANON => STEP (stepFix F)
            | NEUTRAL => NEUTRAL)
      | CBV $ #[A, F] =>
          (case step A of
              STEP A' => STEP (CBV $$ #[A', F])
            | CANON => STEP (stepCbv (A, F))
            | NEUTRAL => NEUTRAL)
      | DECIDE $ #[S, L, R] =>
          (case step S of
              STEP S' => STEP (DECIDE $$ #[S', L, R])
            | CANON => STEP (stepDecideBeta (S, L, R))
            | NEUTRAL => NEUTRAL)
      | NEIGH_IND $ #[M, Z, xypS] =>
          (case step M of
                STEP M' => STEP (NEIGH_IND $$ #[M', Z, xypS])
              | CANON => STEP (stepNeighIndBeta (M, Z, xypS))
              | NEUTRAL => NEUTRAL)
      | NATREC $ #[M, Z, xyS] =>
          (case step M of
                STEP M' => STEP (NATREC $$ #[M', Z, xyS])
              | CANON => STEP (stepNatrecBeta (M, Z, xyS))
              | NEUTRAL => NEUTRAL)
      | WTREE_REC $ #[M, xyzD] =>
          (case step M of
                STEP M' => STEP (WTREE_REC $$ #[M', xyzD])
              | CANON => STEP (stepWTreeRecBeta (M, xyzD))
              | NEUTRAL => NEUTRAL)
      | MATCH_TOKEN toks $ subterms =>
          let
            val M = Vector.sub (subterms, 0)
            val branches =
              Vector.foldri
                (fn (i, tok, dict) =>
                  StringListDict.insert dict tok (Vector.sub (subterms, i + 1)))
                StringListDict.empty
                toks
            val catchAll = Vector.sub (subterms, Vector.length subterms - 1)
          in
            (case step M of
                  STEP M' =>
                  let
                    val subterms' =
                      Vector.tabulate
                        (Vector.length subterms,
                         fn 0 => M'
                          | i => Vector.sub (subterms, i))
                  in
                    STEP (MATCH_TOKEN toks $$ subterms')
                  end
                | CANON => STEP (stepMatchTokenBeta e (M, branches, catchAll))
                | NEUTRAL => NEUTRAL)
          end
      | TEST_ATOM $ #[U,V,S,T] =>
          (case (step U, step V) of
                (STEP U', _) => STEP (TEST_ATOM $$ #[U',V,S,T])
              | (_, STEP V') => STEP (TEST_ATOM $$ #[U,V',S,T])
              | (CANON, CANON) => STEP (stepTestAtomBeta (U, V, S, T))
              | _ => NEUTRAL)
      | SO_APPLY $ #[L, R] =>
          (* This can't come up but I don't think it's wrong
           * Leaving this in here so it's an actual semantics
           * for the core type theory: not just what users
           * can say with the syntax we give.
           *)
          (case project L of
               x \ L => STEP (subst R x L)
             | _ =>
             (case step L of
                 CANON => raise Stuck (SO_APPLY $$ #[L, R])
               | STEP L' => STEP (SO_APPLY $$ #[L', R])
               | NEUTRAL => NEUTRAL))
      | ` _ => NEUTRAL (* Cannot step an open term *)
      | x \ e =>
        (case step e of
            STEP e' => STEP (x \\ e')
          | NEUTRAL => NEUTRAL
          | CANON => NEUTRAL)
      | _ => raise Stuck e

    and step e =
      step' e
      handle CttCalculusInj.Mismatch => NEUTRAL
end

structure Semantics = SmallStep(Syntax)
