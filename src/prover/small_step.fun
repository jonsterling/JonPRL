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
        PAIR $ #[L, R] => R // (L // E)
      | _ => raise Stuck (SPREAD $$ #[P, E])

  fun stepApBeta (F, A) =
    case out F of
        LAM $ #[B] => A // B
      | _ => raise Stuck (AP $$ #[F, A])

  fun stepDecideBeta (S, L, R) =
    case out S of
        INL $ #[A] => A // L
      | INR $ #[B] => B // R
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
      | SO_APPLY $ #[L, R] => raise Stuck e
      | CUSTOM _ $ _ => raise Stuck e (* Require unfolding elsewhere *)
      | ` _ => raise Stuck e (* Cannot step an open term *)
      | _ \ _ =>raise Stuck e (* Cannot step a binder *)
end
