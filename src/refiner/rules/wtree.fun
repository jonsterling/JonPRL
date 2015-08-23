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
      val (UNIV _, #[]) = asApp univ
      val #[C1] = wtree1 ^! WTREE
      val #[C2] = wtree2 ^! WTREE
    in
      [ MAIN |: H >> C.`> EQ $$ #[C1, C2, C.`> CONTAINER $$ #[]]
      ] BY mkEvidence WTREE_EQ
    end

  fun MemEq (_ |: H >> P) =
    let
      val #[sup1, sup2, wtree] = P ^! EQ
      val #[C] = wtree ^! WTREE
      val #[E,xR] = sup1 ^! SUP
      val #[E',yR'] = sup2 ^! SUP

      val B = C.`> REFINEMENT $$ #[C, E]

      val (H', x, R) = ctxUnbind (H, B, xR)
      val R' = yR' // ``x
    in
      [ MAIN |: H >> C.`> EQ $$ #[E, E', C.`> SHAPE $$ #[C]]
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
      val shape = C.`> SHAPE $$ #[cont]
      fun refinement s = C.`> REFINEMENT $$ #[cont, s]

      val (Hx, x, yzD1) = ctxUnbind (H, shape, xyzD1)
      val r = Context.fresh (Hx, Variable.named "r")
      val (Hxy, y, zD1) = ctxUnbind (Hx, C.`> FUN $$ #[refinement (``x), r \\ (C.`> WTREE $$ #[cont])], yzD1)
      val v = Context.fresh (Hxy, Variable.named "v")
      val (Hxyz, z, D1) = ctxUnbind (H, C.`> FUN $$ #[refinement (``x), v \\ (zC // (C.`> AP $$ #[``y, ``v]))], zD1)
      val Cxy = zC // (C.`> SUP $$ #[``x, r \\ (C.`> AP $$ #[``y, ``r])])
      val D2 = xyzD2 // ``x // ``y // ``z
    in
      [ MAIN |: Hxyz >> C.`> EQ $$ #[D1, D2, Cxy]
      ] BY (fn [D] => D.`> WTREE_REC_EQ $$ #[x \\ y \\ z \\ D]
             | _ => raise Refine)
    end

  fun Intro (s, oname) (_ |: H >> P) =
    let
      val #[X] = P ^! WTREE
      val shape = C.`> SHAPE $$ #[X]
      val refinement = C.`> REFINEMENT $$ #[X, s]
      val name =
        Context.fresh (H,
          case oname of
               SOME name => name
             | NONE => Variable.named "r")
    in
      [ AUX |: H >> C.`> MEM $$ #[s, shape]
      , MAIN |: H @@ (name, refinement) >> P
      ] BY (fn [D, E] => D.`> WTREE_INTRO $$ #[s, D, name \\ E]
             | _ => raise Refine)
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
               (Context.fresh (H, Variable.named "s"),
                Context.fresh (H, Variable.named "r"),
                Context.fresh (H, Variable.named "h"))
      val shape = C.`> SHAPE $$ #[X]
      val refinement = C.`> REFINEMENT $$ #[X, ``a]
      val r = Variable.named "r"
      val v = Variable.named "v"
      val sup = C.`> SUP $$ #[``a, r \\ (C.`> AP $$ #[``b, ``r])]
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
