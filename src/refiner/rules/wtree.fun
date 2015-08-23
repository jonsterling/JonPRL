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

end
