functor NatRules(Utils : RULES_UTIL) : NAT_RULES =
struct
  open Utils
  open Goal Sequent Syntax CttCalculus Derivation

  infix $ \ BY ^!
  infix 3 >>
  infix 2 |:
  infix 8 $$ // @@
  infixr 8 \\

  fun NatEq (_ |: H >> P) =
    let
      val #[nat1, nat2, univ] = P ^! EQ
      val (UNIV _, _) = asApp univ
      val #[] = nat1 ^! NAT
      val #[] = nat2 ^! NAT
    in
      [] BY mkEvidence NAT_EQ
    end

  fun NatElim (hyp, onames) (_ |: H >> C) =
    let
      val z = eliminationTarget hyp (H >> C)
      val #[] = Context.lookup H z ^! NAT
      val (n,ih) =
        case onames of
             SOME names => names
           | NONE =>
               (Context.fresh (H, Variable.named "n"),
                Context.fresh (H, Variable.named "ih"))

      val zero = C.`> ZERO $$ #[]
      val succn = C.`> SUCC $$ #[``n]

      val J = Context.empty @@ (n, C.`> NAT $$ #[]) @@ (ih, subst (``n) z C)
      val H' = Context.mapAfter n (Syntax.subst succn z) (Context.interposeAfter H (z, J))
    in
      [ MAIN |: ctxSubst H zero z >> subst zero z C
      , MAIN |: H' >> subst succn z C
      ] BY (fn [D,E] => D.`> NAT_ELIM $$ #[``z, D, n \\ (ih \\ E)]
             | _ => raise Refine)
    end

  fun ZeroEq (_ |: H >> P) =
    let
      val #[zero1, zero2, nat] = P ^! EQ
      val #[] = nat ^! NAT
      val #[] = zero1 ^! ZERO
      val #[] = zero2 ^! ZERO
    in
      [] BY mkEvidence ZERO_EQ
    end

  fun SuccEq (_ |: H >> P) =
    let
      val #[succ1, succ2, nat] = P ^! EQ
      val #[] = nat ^! NAT
      val #[M] = succ1 ^! SUCC
      val #[N] = succ2 ^! SUCC
    in
      [ MAIN |: H >> C.`> EQ $$ #[M, N, C.`> NAT $$ #[]]
      ] BY mkEvidence SUCC_EQ
    end

  fun NatRecEq (ozC, onames) (_ |: H >> P) =
    let
      val #[rec1, rec2, A] = P ^! EQ
      val #[n, zero, succ] = rec1 ^! NATREC
      val #[n', zero', succ'] = rec2 ^! NATREC

      val zC =
        case ozC of
             SOME zC => unify (zC // n) A
           | NONE => Variable.named "z" \\ A

      val (npred, ih) =
          case onames of
              NONE =>
              (Context.fresh (H, Variable.named "n'"),
               Context.fresh (H, Variable.named "ih"))
            | SOME names => names
      val H' = H @@ (npred, C.`> NAT $$ #[]) @@ (ih, zC // (`` npred))
      val succSubst = (succ // ``npred) // ``ih
      val succSubst' = (succ' // ``npred) // ``ih
    in
      [ MAIN |: H >> C.`>EQ $$ #[n, n', C.`> NAT $$ #[]]
      , MAIN |: H >> C.`>EQ $$ #[zero, zero', zC // (C.`> ZERO $$ #[])]
      , MAIN |: H' >> C.`>EQ $$ #[succSubst, succSubst', zC // (C.`> SUCC $$ #[`` npred])]
      ] BY (fn [N, D, E] => D.`> NATREC_EQ $$ #[N, D, npred \\ (ih \\ E)]
             | _ => raise Refine)
    end
end
