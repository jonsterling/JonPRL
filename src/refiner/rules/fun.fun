functor FunRules(Utils : RULES_UTIL) : FUN_RULES =
struct
  open Utils
  open Goal Sequent Syntax CttCalculus Derivation

  infix $ \ BY ^!
  infix 3 >>
  infix 2 |:
  infix 8 $$ // @@
  infixr 8 \\

  val FunEq = QuantifierEq (FUN, FUN_EQ)

  fun FunIntro (oz, ok) (_ |: H >> P) =
    let
      val #[P1, xP2] = P ^! FUN
      val z =
        Context.fresh (H,
          case oz of
               NONE => #1 (unbind xP2)
             | SOME z => z)
      val k = case ok of NONE => inferLevel (H, P1) | SOME k => k
    in
      [ MAIN |: H @@ (z,P1) >> xP2 // `` z
      , AUX |: H >> C.`> MEM $$ #[P1, C.`> (UNIV k) $$ #[]]
      ] BY (fn [D,E] => D.`> FUN_INTRO $$ #[z \\ D, E]
             | _ => raise Refine)
    end

  fun FunElim (hyp, s, onames) (_ |: H >> P) =
    let
      val s = Context.rebind H s
      val f = eliminationTarget hyp (H >> P)
      val #[S, xT] = Context.lookup H f ^! FUN
      val Ts = xT // s
      val (y, z) =
        case onames of
             SOME names => names
           | NONE =>
               (Context.fresh (H, Variable.named "y"),
                Context.fresh (H, Variable.named "z"))

      val fsTs = C.`> EQ $$ #[``y, C.`> AP $$ #[``f, s], Ts]
    in
      [ AUX |: H >> C.`> MEM $$ #[s, S]
      , MAIN |: H @@ (y, Ts) @@ (z, fsTs) >> P
      ] BY (fn [D, E] => D.`> FUN_ELIM $$ #[``f, s, D, y \\ (z \\ E)]
              | _ => raise Refine)
    end

  fun LamEq (oz, ok) (_ |: H >> P) =
    let
      val #[lam, lam', func] = P ^! EQ
      val #[aE] = lam ^! LAM
      val #[bE'] = lam' ^! LAM
      val #[A, cB] = func ^! FUN
      val z =
        Context.fresh (H,
          case oz of
               NONE => #1 (unbind cB)
             | SOME z => z)
      val k = case ok of NONE => inferLevel (H, A) | SOME k => k
    in
      [ MAIN |: H @@ (z,A) >> C.`> EQ $$ #[aE // ``z, bE' // ``z, cB // ``z]
      , AUX |: H >> C.`> MEM $$ #[A, C.`> (UNIV k) $$ #[]]
      ] BY (fn [D, E] => D.`> LAM_EQ $$ #[z \\ D, E]
              | _ => raise Refine)
    end

  fun FunExt (oz, ok) (_ |: H >> P) =
    let
      val #[f1,f2,funty] = P ^! EQ
      val #[S,xT] = funty ^! FUN
      val z =
        Context.fresh (H,
          case oz of
               NONE => #1 (unbind xT)
             | SOME z => z)
      val k = case ok of NONE => inferLevel (H, S) | SOME k => k
    in
      [ MAIN |: H @@ (z, S) >> C.`> EQ $$ #[C.`> AP $$ #[f1,``z], C.`> AP $$ #[f2, ``z], xT // ``z]
      , AUX |: H >> C.`> MEM $$ #[S, C.`> (UNIV k) $$ #[]]
      , AUX |: H >> C.`> MEM $$ #[f1, funty]
      , AUX |: H >> C.`> MEM $$ #[f2, funty]
      ] BY (fn [D,E,F,G] => D.`> FUN_EXT $$ #[z \\ D, E, F, G]
             | _ => raise Refine)
    end

  fun ApEq ofunty (_ |: H >> P) =
    let
      val #[f1t1, f2t2, Tt1] = P ^! EQ
      val #[f1, t1] = f1t1 ^! AP
      val #[f2, t2] = f2t2 ^! AP
      val funty =
        case ofunty of
             NONE => typeLub H (inferType (H, f1)) (inferType (H, f2))
           | SOME funty => Context.rebind H funty
      val #[S, xT] = funty ^! FUN
      val Tt1' = unify (xT // t1) Tt1
    in
      [ MAIN |: H >> C.`> EQ $$ #[f1, f2, funty]
      , MAIN |: H >> C.`> EQ $$ #[t1, t2, S]
      ] BY mkEvidence AP_EQ
    end
end
