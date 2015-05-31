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
       | CUM $ _ => ax

       | EQ_EQ $ _ => ax
       | UNIT_EQ $ _ => ax
       | UNIT_INTRO $ _ => ax
       | UNIT_ELIM $ #[R, E] => extract (E // ax)
       | AX_EQ $ _ => AX $$ #[]

       | PROD_EQ $ _ => ax
       | PROD_INTRO $ #[W, D, E] => PAIR $$ #[W, extract E]
       | PROD_ELIM $ #[R, xyD] => SPREAD $$ #[R, extract xyD]
       | PAIR_EQ $ _ => ax
       | SPREAD_EQ $ _ => ax

       | FUN_EQ $ _ => ax
       | FUN_INTRO $ #[xE, _] => LAM $$ #[extract xE]
       | FUN_ELIM $ #[f, s, D, yzE] =>
           let
             val t = extract yzE
           in
             (t // (AP $$ #[f,s])) // ax
           end
       | LAM_EQ $ _ => ax
       | AP_EQ $ _ => ax

       | ISECT_EQ $ _ => ax
       | ISECT_INTRO $ #[xD, _] => extract (#2 (unbind xD))
       | ISECT_ELIM $ #[f, s, D, yzE] => (extract yzE // f) // ax
       | ISECT_MEMBER_EQ $ _ => ax
       | ISECT_MEMBER_CASE_EQ $ _ => ax

       | HYP_EQ $ _ => ax
       | WITNESS $ #[M, _] => M
       | EQ_SUBST $ #[_, D, _] => extract D

       | SQUASH_EQ $ _ => ax
       | SQUASH_INTRO $ _ => ax
       | SQUASH_ELIM $ _ => ax

       | ADMIT $ #[] => ``(Variable.named "<<<<<ADMIT>>>>>")

       | ` x => `` x
       | x \ E => x \\ extract E

       | _ => raise MalformedEvidence E
end

structure Extract = Extract(Syntax)
