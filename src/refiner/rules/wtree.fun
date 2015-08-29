functor WTreeRules(Utils : RULES_UTIL) : WTREE_RULES =
struct
  open Utils
  open Goal Sequent Syntax CttCalculus Derivation

  infix $ \ BY ^!
  infix 3 >>
  infix 2 |:
  infix 8 $$ // @@
  infixr 8 \\

  fun Eq (_ |: H >> P) =
    let
      val #[wtree1,wtree2,univ] = P ^! EQ
      val (UNIV i, #[]) = asApp univ
      val #[C1] = wtree1 ^! WTREE
      val #[C2] = wtree2 ^! WTREE
    in
      [ MAIN |: H >> C.`> EQ $$ #[C1, C2, C.`> (CONTAINER i) $$ #[]]
      ] BY mkEvidence WTREE_EQ
    end

  fun MemEq (_ |: H >> P) =
    let
      val #[sup1, sup2, wtree] = P ^! EQ
      val #[C] = wtree ^! WTREE

      val #[ext1] = sup1 ^! SUP
      val #[ext2] = sup2 ^! SUP

      val E = C.`> DOM $$ #[ext1]
      val E' = C.`> DOM $$ #[ext2]

      val x = Context.fresh (H, Variable.named "x")
      val R = C.`> PROJ $$ #[ext1, ``x]
      val R' = C.`> PROJ $$ #[ext2, ``x]
      val B = C.`> PROJ $$ #[C, E]
      val H' = H @@ (x, B)
    in
      [ MAIN |: H >> C.`> EQ $$ #[E, E', C.`> DOM $$ #[C]]
      , MAIN |: H' >> C.`> EQ $$ #[R, R', wtree]
      ] BY (fn [D, E] => D.`> WTREE_MEM_EQ $$ #[D, x \\ E]
             | _ => raise Refine)
    end

  fun RecEq (ocont, zC) (_ |: H >> P) =
    let
      val #[rec1, rec2, C] = P ^! EQ
      val #[t1, xyzD1] = rec1 ^! WTREE_REC
      val #[t2, xyzD2] = rec2 ^! WTREE_REC

      val C' = unify C (zC // t1)

      val cont =
        case ocont of
             SOME cont => cont
           | NONE =>
             let
               val ty = typeLub H (inferType (H, t1)) (inferType (H, t2))
               val #[cont] = ty ^! WTREE
             in
               cont
             end
      val shape = C.`> DOM $$ #[cont]
      fun refinement s = C.`> PROJ $$ #[cont, s]

      val (Hx, x, yzD1) = ctxUnbind (H, shape, xyzD1)
      val r = Context.fresh (Hx, Variable.named "r")
      val (Hxy, y, zD1) = ctxUnbind (Hx, C.`> FUN $$ #[refinement (``x), r \\ (C.`> WTREE $$ #[cont])], yzD1)
      val v = Context.fresh (Hxy, Variable.named "v")
      val (Hxyz, z, D1) = ctxUnbind (Hxy, C.`> FUN $$ #[refinement (``x), v \\ (zC // (C.`> AP $$ #[``y, ``v]))], zD1)
      val Cxy = zC // (C.`> SUP $$ #[C.`> EXTEND $$ #[``x, r \\ (C.`> AP $$ #[``y, ``r])]])
      val D2 = xyzD2 // ``x // ``y // ``z
    in
      [ MAIN |: Hxyz >> C.`> EQ $$ #[D1, D2, Cxy]
      , AUX |: H >> C.`> EQ $$ #[t1, t2, C.`> WTREE $$ #[cont]]
      ] BY (fn [D, E] => D.`> WTREE_REC_EQ $$ #[x \\ y \\ z \\ D, E]
             | _ => raise Refine)
    end

  fun Intro (_ |: H >> P) =
    let
      val #[X] = P ^! WTREE
    in
      [ MAIN |: H >> C.`> EXTENSION $$ #[X, P]
      ] BY mkEvidence WTREE_INTRO
    end

  fun Elim (hyp, onames) (_ |: H >> C) =
    let
      val z = eliminationTarget hyp (H >> C)
      val wtree = Context.lookup H z
      val #[X] = wtree ^! WTREE
      val (a, b, c) =
        case onames of
             SOME names => names
           | NONE =>
               (Context.fresh (H, Variable.named "a"),
                Context.fresh (H, Variable.named "b"),
                Context.fresh (H, Variable.named "c"))
      val shape = C.`> DOM $$ #[X]
      val refinement = C.`> PROJ $$ #[X, ``a]
      val r = Context.fresh (H, Variable.named "r")
      val v = Context.fresh (H, Variable.named "v")
      val sup = C.`> SUP $$ #[C.`> EXTEND $$ #[``a, r \\ (C.`> AP $$ #[``b, ``r])]]
      val J =
        Context.empty
          @@ (a, shape)
          @@ (b, C.`> FUN $$ #[refinement, r \\ wtree])
          @@ (c, C.`> FUN $$ #[refinement, v \\ subst (C.`> AP $$ #[``b, ``v]) z C])
      val H' = ctxSubst (Context.interposeAfter H (z, J)) sup z
    in
      [ MAIN |: H' >> subst sup z C
      ] BY (fn [D] => D.`> WTREE_ELIM $$ #[``z, a \\ b \\ c \\ D]
             | _ => raise Refine)
    end
end
