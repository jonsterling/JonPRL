functor UnivRules(Utils : RULES_UTIL) : UNIV_RULES =
struct
  open Utils
  open Goal Sequent Syntax CttCalculus Derivation

  infix $ \ BY ^!
  infix 3 >>
  infix 2 |:
  infix 8 $$ // @@
  infixr 8 \\

  fun Cum ok : tactic =
    fn (_ |: H >> P) =>
      let
        val #[A, B, univ] = P ^! EQ
        val (UNIV l, #[]) = asApp univ
        val k = case ok of NONE => Level.max (inferLevel (H, A), inferLevel (H, B)) | SOME k => k
        val _ = Level.assertLt (k, l)
      in
        [MAIN |: H >> C.`> EQ $$ #[A,B, C.`> (UNIV k) $$ #[]]] BY mkEvidence CUM
      end

  fun Eq (_ |: H >> P) =
    let
      val #[univ1, univ2, univ3] = P ^! EQ
      val (UNIV l, #[]) = asApp univ1
      val (UNIV l', #[]) = asApp univ2
      val (UNIV k, #[]) = asApp univ3
      val _ = Level.assertEq (l, l')
      val _ = Level.assertLt (l, k)
    in
      [] BY mkEvidence (UNIV_EQ l)
    end
end
