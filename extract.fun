functor Extract (Syn : ABT_UTIL where Operator = Operator) : EXTRACT =
struct
  type evidence = Syn.t
  type term = Syn.t

  exception MalformedEvidence of Syn.t

  open Syn Operator
  infix $ \ $$ \\ //

  val ax = AX $$ #[]

  fun extract E =
    case out E of
         UNIV_EQ $ _ => ax
       | VOID_EQ $ _ => ax
       | VOID_ELIM $ _ => ax

       | UNIT_EQ $ _ => ax
       | UNIT_INTRO $ _ => ax
       | UNIT_ELIM $ #[R, E] => MATCH_UNIT $$ #[extract R, extract E]
       | AX_EQ $ _ => AX $$ #[]

       | PROD_EQ $ _ => ax
       | PROD_INTRO $ #[W, D, E] => PAIR $$ #[W, extract E]
       | PROD_ELIM $ #[R, xyD] => SPREAD $$ #[R, extract xyD]
       | PAIR_EQ $ _ => ax

       | FUN_EQ $ _ => ax
       | FUN_INTRO $ #[xE, _] => LAM $$ #[extract xE]
       | LAM_EQ $ _ => ax

       | HYP_EQ $ _ => ax
       | WITNESS $ #[M, _] => M

       | ` x => `` x
       | x \ E => x \\ extract E

       | _ => raise MalformedEvidence E
end
