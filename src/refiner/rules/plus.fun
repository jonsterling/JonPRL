functor PlusRules(Utils : RULES_UTIL) : PLUS_RULES =
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
      val #[L, R, U] = P ^! EQ
      val (UNIV _, #[]) = asApp U
      val #[A, B] = L ^! PLUS
      val #[A', B'] = R ^! PLUS
    in
       [ MAIN |: H >> C.`> EQ $$ #[A, A', U]
       , MAIN |: H >> C.`> EQ $$ #[B, B', U]
       ] BY (fn [L, R] => D.`> PLUS_EQ $$ #[L, R]
              | _ => raise Refine)
    end

  fun IntroL x (_ |: H >> P) =
    let
      val #[A, B] = P ^! PLUS
      val k = case x of SOME k => k | NONE => inferLevel (H, B)
    in
      [ MAIN |: H >> A
      , AUX |: H >> C.`> MEM $$ #[B, C.`> (UNIV k) $$ #[]]
      ] BY (fn [InA, WfB] => D.`> PLUS_INTROL $$ #[InA, WfB]
             | _ => raise Refine)
    end

  fun IntroR x (_ |: H >> P) =
    let
      val #[A, B] = P ^! PLUS
      val k = case x of SOME k => k | NONE => inferLevel (H, A)
    in
      [ MAIN |: H >> B
      , AUX |: H >> C.`> MEM $$ #[A, C.`> (UNIV k) $$ #[]]
      ] BY (fn [InB, WfA] => D.`> PLUS_INTROR $$ #[InB, WfA]
             | _ => raise Refine)
    end

  fun Elim (i, onames) (_ |: H >> P) =
    let
      val z = eliminationTarget i (H >> P)
      val #[A, B] = Context.lookup H z ^! PLUS
      val (s, t) =
          case onames of
              SOME names => names
            | NONE => (Context.fresh (H, Variable.named "s"),
                       Context.fresh (H, Variable.named "t"))
      val withs = C.`> INL $$ #[``s]
      val witht = C.`> INR $$ #[``t]
      val H's = ctxSubst (Context.interposeAfter H (z, Context.empty @@ (s, A)))
                         withs z
      val H't = ctxSubst (Context.interposeAfter H (z, Context.empty @@ (t, B)))
                         witht z
    in
      [ MAIN |: H's >> subst withs z P
      , MAIN |: H't >> subst witht z P
      ] BY (fn [L, R] => D.`> PLUS_ELIM $$ #[``z, s \\ L, t \\ R]
             | _ => raise Refine)
    end

  fun InlEq x (_ |: H >> P) =
    let
      val #[M, N, T] = P ^! EQ
      val #[A, B] = T ^! PLUS
      val #[M'] = M ^! INL
      val #[N'] = N ^! INL
      val k = case x of SOME k => k | NONE => inferLevel (H, B)
    in
      [ MAIN |: H >> C.`> EQ $$ #[M', N', A]
      , AUX |: H >> C.`> MEM $$ #[B, C.`> (UNIV k) $$ #[]]
      ] BY (fn [In, Wf] => D.`> INL_EQ $$ #[In, Wf]
             | _ => raise Refine)
    end

  fun InrEq x (_ |: H >> P) =
    let
      val #[M, N, T] = P ^! EQ
      val #[A, B] = T ^! PLUS
      val #[M'] = M ^! INR
      val #[N'] = N ^! INR
      val k = case x of SOME k => k | NONE => inferLevel (H, A)
    in
      [ MAIN |: H >> C.`> EQ $$ #[M', N', B]
      , AUX |: H >> C.`> MEM $$ #[A, C.`> (UNIV k) $$ #[]]
      ] BY (fn [In, Wf] => D.`> INR_EQ $$ #[In, Wf]
             | _ => raise Refine)
    end

  fun DecideEq (A, B, x) (_ |: H >> P) =
    let
      val #[M, N, T] = P ^! EQ
      val #[M', sL, tR] = M ^! DECIDE
      val #[N', sL', tR'] = N ^! DECIDE
      val (s, t, eq) =
          case x of
              SOME names => names
            | NONE => (Context.fresh (H, Variable.named "s"),
                       Context.fresh (H, Variable.named "t"),
                       Context.fresh (H, Variable.named "eq"))
      val H's = H @@ (s, A)
                  @@ (eq, C.`> EQ $$ #[M', C.`> INL $$ #[``s], C.`> PLUS $$ #[A, B]])
      val H't = H @@ (t, B)
                  @@ (eq, C.`> EQ $$ #[M', C.`> INR $$ #[``t], C.`> PLUS $$ #[A, B]])
    in
      [ MAIN |: H >> C.`> EQ $$ #[M', N', C.`> PLUS $$ #[A, B]]
      , MAIN |: H's >> C.`> EQ $$ #[subst1 sL (``s), subst1 sL' (``s), T]
      , MAIN |: H't >> C.`> EQ $$ #[subst1 tR (``t), subst1 tR' (``t), T]
      ] BY (fn [EqM, EqL, EqR] =>
               D.`> DECIDE_EQ $$ #[EqM, eq \\ (s \\ EqR), eq \\ (t \\ EqL)]
             | _ => raise Refine)
    end
end
