functor Extract (Syn : ABT_UTIL where type Operator.t = StringVariable.t OperatorType.operator) : EXTRACT =
struct
  type evidence = Syn.t
  type term = Syn.t

  exception MalformedEvidence of Syn.t

  open Syn
  open Operator
  open OperatorType
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
       | UNIT_ELIM $ #[R, E] => extract E
       | AX_EQ $ _ => AX $$ #[]
       | EQ_SYM $ _ => ax

       | PROD_EQ $ _ => ax
       | PROD_INTRO $ #[M, D, E, xF] => PAIR $$ #[M, extract E]
       | IND_PROD_INTRO $ #[D,E] => PAIR $$ #[extract D, extract E]
       | PROD_ELIM $ #[R, xyD] => SPREAD $$ #[R, extract xyD]
       | PAIR_EQ $ _ => ax
       | SPREAD_EQ $ _ => ax

       | PLUS_EQ $ _ => ax
       | INL_EQ $ _ => ax
       | INR_EQ $ _ => ax
       | DECIDE_EQ $ _ => ax
       | PLUS_INTROL $ #[E, _] => INL $$ #[extract E]
       | PLUS_INTROR $ #[E, _] => INR $$ #[extract E]
       | PLUS_ELIM $ #[E, xD, xF] =>
         DECIDE $$ #[extract E, extract xD, extract xF]

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
       | FUN_EXT $ _ => ax

       | ISECT_EQ $ _ => ax
       | ISECT_INTRO $ #[xD, _] => extract (#2 (unbind xD))
       | ISECT_ELIM $ #[f, s, D, yzE] => (extract yzE // f) // ax
       | ISECT_MEMBER_EQ $ _ => ax
       | ISECT_MEMBER_CASE_EQ $ _ => ax

       | SUBSET_EQ $ _ => ax
       | SUBSET_INTRO $ #[w,_,_,_] => w
       | IND_SUBSET_INTRO $ #[D, _] => extract D
       | SUBSET_ELIM $ #[R, stD] => extract (stD // R) // ax
       | SUBSET_MEMBER_EQ $ _ => ax

       | IR_EQ $ _ => ax
       | IR_INTRO_IOTA $ #[D,E] => IR_IOTA $$ #[extract D]
       | IR_INTRO_SIGMA $ #[S,D,xE] => IR_SIGMA $$ #[S, extract xE]
       | IR_INTRO_DELTA $ #[S,D,xE] => IR_DELTA $$ #[S, extract xE]
       | IR_IOTA_EQ $ _ => ax
       | IR_SIGMA_EQ $ _ => ax
       | IR_DELTA_EQ $ _ => ax

       | HYP_EQ $ _ => ax
       | WITNESS $ #[M, _] => M
       | EQ_SUBST $ #[_, D, _] => extract D

       | ADMIT $ #[] => ``(Variable.named "<<<<<ADMIT>>>>>")

       | ` x => `` x
       | x \ E => x \\ extract E

       | _ => raise MalformedEvidence E
end

structure Extract = Extract(Syntax)
