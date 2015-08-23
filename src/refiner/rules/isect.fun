functor ISectRules(Utils : RULES_UTIL) : ISECT_RULES =
struct
  open Utils
  open Goal Sequent Syntax CttCalculus Derivation

  infix $ \ BY ^!
  infix 3 >>
  infix 2 |:
  infix 8 $$ // @@
  infixr 8 \\

  val Eq = QuantifierEq (ISECT, ISECT_EQ)

  fun Intro (oz, ok) (_ |: H >> P) =
    let
      val #[P1, xP2] = P ^! ISECT
      val z =
        Context.fresh (H,
          case oz of
               NONE => #1 (unbind xP2)
             | SOME z => z)
      val k = case ok of NONE => inferLevel (H, P1) | SOME k => k
      val H' = Context.insert H z Visibility.Hidden P1
    in
      [ MAIN |: H' >> xP2 // `` z
      , AUX |: H >> C.`> MEM $$ #[P1, C.`> (UNIV k) $$ #[]]
      ] BY (fn [D,E] => D.`> ISECT_INTRO $$ #[z \\ D, E]
             | _ => raise Refine)
    end

  fun Elim (hyp, s, onames) (_ |: H >> P) =
    let
      val s = Context.rebind H s
      val f = eliminationTarget hyp (H >> P)

      val #[S, xT] = Context.lookup H f ^! ISECT
      val Ts = xT // s
      val (y, z) =
        case onames of
             SOME names => names
           | NONE =>
               (Context.fresh (H, Variable.named "y"),
                Context.fresh (H, Variable.named "z"))

      val fsTs = C.`> EQ $$ #[``y, ``f, Ts]
    in
      [ AUX |: H >> C.`> MEM $$ #[s, S]
      , MAIN |: H @@ (y, Ts) @@ (z, fsTs) >> P
      ] BY (fn [D, E] => D.`> ISECT_ELIM $$ #[``f, s, D, y \\ (z \\ E)]
              | _ => raise Refine)
    end

  fun MemberEq (oz, ok) (_ |: H >> P) =
    let
      val #[M,N,A] = P ^! EQ
      val #[P1, xP2] = A ^! ISECT
      val z =
        Context.fresh (H,
          case oz of
               NONE => #1 (unbind xP2)
             | SOME z => z)
      val k = case ok of NONE => inferLevel (H, P1) | SOME k => k
      val H' = Context.insert H z Visibility.Hidden P1
    in
      [ MAIN |: H' >> C.`> EQ $$ #[M,N, xP2 // ``z]
      , AUX |: H >> C.`> MEM $$ #[P1, C.`> (UNIV k) $$ #[]]
      ] BY (fn [D, E] => D.`> ISECT_MEMBER_EQ $$ #[z \\ D, E]
             | _ => raise Refine)
    end

  fun MemberCaseEq (oisect, t) (_ |: H >> P) =
    let
      val t = Context.rebind H t
      val #[F1,F2, Tt] = P ^! EQ
      val isect =
        case oisect of
             SOME isect => isect
           | NONE => typeLub H (inferType (H, F1)) (inferType (H, F2))

      val #[S, xT] = isect ^! ISECT
      val _ = unify Tt (xT // t)
    in
      [ MAIN |: H >> C.`> EQ $$ #[F1, F2, isect]
      , MAIN |: H >> C.`> MEM $$ #[t, S]
      ] BY mkEvidence ISECT_MEMBER_CASE_EQ
    end
end
