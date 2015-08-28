functor ContainerExtensionRules(Utils : RULES_UTIL) : CONTAINER_EXTENSION_RULES =
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
      val #[ext1, ext2, univ] = P ^! EQ
      val (UNIV i, _) = asApp univ
      val #[C1, X1] = ext1 ^! EXTENSION
      val #[C2, X2] = ext2 ^! EXTENSION
    in
      [ MAIN |: H >> C.`> EQ $$ #[C1, C2, C.`> (CONTAINER i) $$ #[]]
      , MAIN |: H >> C.`> EQ $$ #[X1, X2, univ]
      ] BY mkEvidence EXTENSION_EQ
    end

  fun MemEq (_ |: H >> P) =
    let
      val #[extend1, extend2, extension] = P ^! EQ
      val #[C, X] = extension ^! EXTENSION
      val #[d1, pX1] = extend1 ^! EXTEND
      val #[d2, qX2] = extend1 ^! EXTEND
      val dom = C.`> DOM $$ #[C]
      val (H', p, X1) = ctxUnbind (H, dom, pX1)
      val X2 = qX2 // ``p
    in
      [ MAIN |: H >> C.`> EQ $$ #[d1, d2, dom]
      , MAIN |: H' >> C.`> EQ $$ #[X1, X2, X]
      ] BY (fn [D, E] => D.`> EXTEND_EQ $$ #[D, p \\ E]
             | _ => raise Refine)
    end

  fun Elim (hyp, onames) (_ |: H >> P) =
    let
      val z = eliminationTarget hyp (H >> P)
      val #[F, X] = Context.lookup H z ^! EXTENSION
      val (s, t) =
        case onames of
             SOME names => names
           | NONE =>
               (Context.fresh (H, Variable.named "s"),
                Context.fresh (H, Variable.named "t"))

      val p = Context.fresh (H, Variable.named "p")
      val st = C.`> EXTEND $$ #[``s, p \\ (C.`> AP $$ #[``t, ``p])]
      val J =
        Context.empty
          @@ (s, C.`> DOM $$ #[F])
          @@ (t, C.`> FUN $$ #[C.`> PROJ $$ #[F, ``s], p \\ X])
      val H' = ctxSubst (Context.interposeAfter H (z, J)) st z
    in
      [ MAIN |: H' >> subst st z P
      ] BY (fn [D] => D.`> EXTENSION_ELIM $$ #[``z, s \\ (t \\ D)]
             | _ => raise Refine)
    end
end
