functor Extract (Syn : ABT_UTIL where type Operator.t = UniversalOperator.t) : EXTRACT =
struct
  type evidence = Syn.t
  type term = Syn.t

  exception MalformedEvidence of Syn.t

  open CttCalculus CttCalculusInj Derivation
  structure DerivationView = RestrictAbtView
    (structure Abt = Syn and Injection = DerivationInj)

  open Syn DerivationView
  infix $ \ $$ \\ //

  val ax = `> AX $$ #[]

  fun extract E =
    case project E of
         UNIV_EQ _ $ _ => ax
       | CUM $ _ => ax

       | EQ_EQ $ _ => ax
       | EQ_EQ_BASE $ _ => ax
       | EQ_MEMBER_EQ $ _ => ax
       | EQ_SYM $ _ => ax
       | CEQUAL_EQ $ _ => ax
       | CEQUAL_MEMBER_EQ $ _ => ax
       | CEQUAL_SYM $ _ => ax
       | CEQUAL_STEP $ _ => ax
       | CEQUAL_SUBST $ #[D, E] => extract E
       | CEQUAL_STRUCT _ $ _ => ax (* Thank god *)
       | CEQUAL_APPROX $ _ => ax
       | CEQUAL_ELIM $ _ => ax
       | APPROX_MEMBER_EQ $ _ => ax
       | APPROX_EQ $ _ => ax
       | APPROX_EXT_EQ $ _ => ax
       | APPROX_REFL $ _ => ax
       | APPROX_ELIM $ #[_, D] => extract D
       | BOTTOM_DIVERGES $ _ => ax (* could be anything because one hypothesis is false *)
       | ASSUME_HAS_VALUE $ _ => ax

       | BASE_INTRO $ _ => ax
       | BASE_EQ $ _ => ax
       | BASE_MEMBER_EQ _ $ _ => ax
       | ATOM_SUBTYPE_BASE $ _ => ax
       | BASE_ELIM_EQ $ #[D] => extract (D // ax)

       | IMAGE_EQ $ _ => ax
       | IMAGE_MEM_EQ $ _ => ax
       | IMAGE_ELIM $ #[wD] =>
           let
             (* NOTE: this is a very strange rule, which is
              * (proof-theoretically) perhaps a bit suspect. Image elimination
              * is only constructive in case the conclusion is proof-irrelevant,
              * and so one way to formulate the rule would be to use [ax] as the
              * extract. I think the extraction below, however, is a little bit
              * more sensible: first, we extract the derivation that has a free
              * variable <w> in it, and then since we required that <w> be a
              * "hidden" variable, we are free to substitute it with [ax] at the
              * end. *)
             val (w,D) = unbind wD
           in
             (w \\ extract D) // ax
           end
       | IMAGE_EQ_IND $ _ => ax

       | PER_EQ $ _ => ax
       | PER_MEM_EQ $ _ => ax
       | PER_ELIM $ #[yD,E] =>
           let
             val (y,D) = unbind yD
           in
             (y \\ extract D) // ax
           end

       | UNHIDE $ _ => ax

       | POINTWISE_FUNCTIONALITY $ #[abD,_] =>
           let val (a,bD) = unbind abD
               val (b,D) = unbind bD
           in ((a \\ (b \\ extract D)) // ax) // ax
           end

       | ATOM_EQ $ _ => ax
       | TOKEN_EQ $ _ => ax
       | MATCH_TOKEN_EQ toks $ Ds => ax
       | TEST_ATOM_EQ $ _ => ax
       | TEST_ATOM_REDUCE_LEFT $ _ => ax
       | TEST_ATOM_REDUCE_RIGHT $ _ => ax

       | PROD_EQ $ _ => ax
       | PROD_INTRO $ #[M, D, E, xF] => `> PAIR $$ #[M, extract E]
       | IND_PROD_INTRO $ #[D,E] => `> PAIR $$ #[extract D, extract E]
       | PROD_ELIM $ #[R, xyD] => `> SPREAD $$ #[R, extract xyD]
       | PAIR_EQ $ _ => ax
       | SPREAD_EQ $ _ => ax

       | PLUS_EQ $ _ => ax
       | INL_EQ $ _ => ax
       | INR_EQ $ _ => ax
       | DECIDE_EQ $ _ => ax
       | PLUS_INTROL $ #[E, _] => `> INL $$ #[extract E]
       | PLUS_INTROR $ #[E, _] => `> INR $$ #[extract E]
       | PLUS_ELIM $ #[E, xD, xF] =>
         `> DECIDE $$ #[extract E, extract xD, extract xF]

       | FUN_EQ $ _ => ax
       | FUN_INTRO $ #[xE, _] => `> LAM $$ #[extract xE]
       | FUN_ELIM $ #[f, s, D, yzE] =>
           let
             val t = extract yzE
           in
             (t // (`> AP $$ #[f,s])) // ax
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

       | NAT_EQ $ _ => ax
       | NAT_ELIM $ #[z, D, xyE] => `> NATREC $$ #[z, extract D, extract xyE]
       | ZERO_EQ $ _ => ax
       | SUCC_EQ $ _ => ax
       | NATREC_EQ $ _ => ax

       | CONTAINER_EQ $ _ => ax
       | CONTAINER_MEM_EQ $ _ => ax
       | CONTAINER_ELIM $ #[R, xyD] =>
           let
             val v = Variable.named "v"
           in
             xyD // (`> DOM $$ #[R]) // (`> LAM $$ #[v \\ (`> PROJ $$ #[R, ``v])])
           end

       | EXTENSION_EQ $ _ => ax
       | EXTEND_EQ $ _ => ax
       | EXTENSION_ELIM $ #[R, xyD] =>
           let
             val v = Variable.named "v"
           in
             xyD // (`> DOM $$ #[R]) // (`> LAM $$ #[v \\ (`> PROJ $$ #[R, ``v])])
           end

       | NEIGH_EQ $ _ => ax
       | NEIGH_NIL_EQ $ _ => ax
       | NEIGH_SNOC_EQ $ _ => ax
       | NEIGH_IND_EQ $ _ => ax
       | NEIGH_ELIM $ #[N,nilCase,snocCase] =>
           `> NEIGH_IND $$ #[N, extract nilCase, extract snocCase]

       | WTREE_EQ $ _ => ax
       | WTREE_MEM_EQ $ _ => ax
       | WTREE_REC_EQ $ _ => ax
       | WTREE_INTRO $ #[D] => `> SUP $$ #[extract D]
       | WTREE_ELIM $ #[z, xyzD] => `> WTREE_REC $$ #[z, extract xyzD]

       | HYP_EQ $ _ => ax
       | WITNESS $ #[M, _] => M
       | EQ_SUBST $ #[_, D, _] => extract D

       | FIAT $ #[] => raise Fail "FIAT may not appear in extract"

       | LEMMA {label} $ _ => ``(Variable.named label)
       | ASSERT $ #[D, E] => extract E // extract D

       | ` x => `` x
       | x \ E => x \\ extract E

       | _ => (print ("Malformed evidence: " ^ Syn.toString E); raise MalformedEvidence E)
end

structure Extract = Extract(Syntax)
