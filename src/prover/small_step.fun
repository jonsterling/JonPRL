functor SmallStep (Syn : ABT_UTIL where type Operator.t = StringVariable.t OperatorType.operator)
        : SMALL_STEP =
struct
  type syn = Syn.t

  open Syn
  open Operator
  open OperatorType
  infix $ \ $$ \\ //


  exception Stuck of Syn.t
  datatype t = STEP of Syn.t | CANON

  fun stepSpreadBeta (P, E) =
    case out P of
        PAIR $ #[L, R] => (E // L) // R
      | _ => raise Stuck (SPREAD $$ #[P, E])

  fun stepApBeta (F, A) =
    case out F of
        LAM $ #[B] => B // A
      | _ => raise Stuck (AP $$ #[F, A])

  fun stepDecideBeta (S, L, R) =
    case out S of
        INL $ #[A] => L // A
      | INR $ #[B] => R // B
      | _ => raise Stuck (DECIDE $$ #[S, L, R])

  fun step e =
    case out e of
        UNIV _ $ _ => CANON
      | VOID $ _ => CANON
      | UNIT $ _ => CANON
      | AX $ _ => CANON
      | PROD $ _ => CANON
      | PAIR $ _ => CANON
      | SPREAD $ #[P, E] =>
        STEP (
          case step P of
              STEP P' => SPREAD $$ #[P', E]
            | CANON => stepSpreadBeta (P, E)
        )
      | FUN $ _ => CANON
      | LAM $ _ => CANON
      | AP $ #[L, R] =>
        STEP (
          case step L of
              STEP L' => AP $$ #[L', R]
            | CANON => stepApBeta (L, R)
        )
      | ISECT $ _ => CANON
      | EQ $ _ => CANON
      | MEM $ _ => CANON
      | SUBSET $ _ => CANON
      | PLUS $ _ => CANON
      | INL $ _ => CANON
      | INR $ _ => CANON
      | DECIDE $ #[S, L, R] =>
        STEP (
          case step S of
              STEP S' => DECIDE $$ #[S', L, R]
            | CANON => stepDecideBeta (S, L, R)
        )
      | SO_APPLY $ #[L, R] => (
          (* This can't come up but I don't think it's wrong
           * Leaving this in here so it's an actual semantics
           * for the core type theory: not just what users
           * can say with the syntax we give.
           *)
          case out L of
            x \ L => STEP (subst R x L)
           | _ =>
             case step L of
               CANON => raise Stuck (SO_APPLY $$ #[L, R])
              | STEP L' => STEP (SO_APPLY $$ #[L', R])
      )
      | CUSTOM _ $ _ => raise Stuck e (* Require unfolding elsewhere *)
      | ` _ => raise Stuck e (* Cannot step an open term *)
      | _ \ _ => raise Stuck e (* Cannot step a binder *)
      | _ => raise Stuck e
end
