functor EqRules(Utils : RULES_UTIL) : EQ_RULES =
struct
  open Utils
  open Goal Sequent Syntax CttCalculus Derivation

  infix $ \ BY ^!
  infix 3 >>
  infix 2 |:
  infix 8 $$ // @@
  infixr 8 \\

  fun EqEq (_ |: H >> P) =
    let
      val #[E1, E2, univ] = P ^! EQ
      val (UNIV k, #[]) = asApp univ
      val #[M,N,A] = E1 ^! EQ
      val #[M',N',A'] = E2 ^! EQ
    in
      [ MAIN |: H >> C.`> EQ $$ #[A,A',univ]
      , MAIN |: H >> C.`> EQ $$ #[M,M',A]
      , MAIN |: H >> C.`> EQ $$ #[N,N',A]
      ] BY mkEvidence EQ_EQ
    end

  fun EqEqBase (_ |: H >> P) =
    let
      val #[E1, E2, univ] = P ^! EQ
      val (UNIV k, #[]) = asApp univ
      val #[M,N,A] = E1 ^! EQ
      val #[M',N',A'] = E2 ^! EQ
      val bas = C.`> BASE $$ #[]
      val img = C.`> BUNION $$ #[A, bas]
    in
      [ MAIN |: H >> C.`> EQ $$ #[A,A',univ]
      , MAIN |: H >> C.`> EQ $$ #[M,M',img]
      , MAIN |: H >> C.`> EQ $$ #[N,N',img]
      ] BY mkEvidence EQ_EQ_BASE
    end

  fun EqMemEq (_ |: H >> P) =
    let
      val #[M, N, E] = P ^! EQ
      val #[] = M ^! AX
      val #[] = N ^! AX
      val #[M', N', T] = E ^! EQ
    in
      [ MAIN |: H >> E
      ] BY mkEvidence EQ_MEMBER_EQ
    end
end
