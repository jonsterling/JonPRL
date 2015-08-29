functor ContainerRules(Utils : RULES_UTIL) : CONTAINER_RULES =
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
      val #[cont1,cont2,univ] = P ^! EQ
      val (CONTAINER i, _) = asApp cont1
      val (CONTAINER j, _) = asApp cont2
      val true = i = j
      val (UNIV k, _) = asApp univ
      val true = k = Level.succ i
    in
      [] BY mkEvidence CONTAINER_EQ
    end

  fun MemEq (_ |: H >> P) =
    let
      val #[mkcont1, mkcont2, cont] = P ^! EQ
      val (CONTAINER i, _) = asApp cont
      val #[dom, xProj] = mkcont1 ^! MAKE_CONTAINER
      val #[dom', yProj'] = mkcont1 ^! MAKE_CONTAINER
      val (H', x, proj) = ctxUnbind (H, dom, xProj)
      val proj' = yProj' // ``x
      val univ = C.`> (UNIV i) $$ #[]
    in
      [ MAIN |: H >> C.`> EQ $$ #[dom, dom', univ]
      , MAIN |: H' >> C.`> EQ $$ #[proj, proj', univ]
      ] BY (fn [D, E] => D.`> CONTAINER_MEM_EQ $$ #[D, x \\ E]
             | _ => raise Refine)
    end

  fun Elim (hyp, onames) (_ |: H >> P) =
    let
      val z = eliminationTarget hyp (H >> P)
      val (CONTAINER i, _) = asApp (Context.lookup H z)
      val (s, t) =
        case onames of
             SOME names => names
           | NONE =>
               (Context.fresh (H, Variable.named "s"),
                Context.fresh (H, Variable.named "t"))

      val p = Context.fresh (H, Variable.named "p")
      val st = C.`> MAKE_CONTAINER $$ #[``s, p \\ (C.`> AP $$ #[``t, ``p])]
      val univ = C.`> (UNIV i) $$ #[]
      val J =
        Context.empty
          @@ (s, univ)
          @@ (t, C.`> FUN $$ #[``s, p \\ univ])
      val H' = ctxSubst (Context.interposeAfter H (z, J)) st z
    in
      [ MAIN |: H' >> subst st z P
      ] BY (fn [D] => D.`> CONTAINER_ELIM $$ #[``z, s \\ (t \\ D)]
             | _ => raise Refine)
    end

end
