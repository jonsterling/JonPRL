functor BaseRules(Utils : RULES_UTIL) : BASE_RULES =
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
      val #[M, N, U] = P ^! EQ
      val #[] = M ^! BASE
      val #[] = N ^! BASE
      val (UNIV _, _) = asApp U
    in
      [] BY (fn [] => D.`> BASE_EQ $$ #[]
              | _ => raise Refine)
    end

  fun Intro (_ |: H >> P) =
    let
      val #[] = P ^! BASE
    in
      [] BY (fn [] => D.`> BASE_INTRO $$ #[]
              | _ => raise Refine)
    end

  fun MemberEq (_ |: H >> P) =
    let
      val #[M, N, U] = P ^! EQ
      val #[] = U ^! BASE
      val free = freeVariables M
      val n = length free
      val L = List.map (fn v => AUX |: H >> C.`> MEM $$ #[``v, U]) free
    in
      ((MAIN |: H >> C.`> CEQUAL $$ #[M, N]) :: L)
	  BY mkEvidence (BASE_MEMBER_EQ n)
    end

  fun AtomSubtypeBase (_ |: H >> P) =
    let
      val #[M, N, U] = P ^! EQ
      val #[] = U ^! BASE
    in
      [MAIN |: H >> C.`> EQ $$ #[M, N, C.`> ATOM $$ #[]]]
	  BY mkEvidence ATOM_SUBTYPE_BASE
    end

  fun ElimEq (hyp, z) (_ |: H >> P) =
    let
      val eq = eliminationTarget hyp (H >> P)
      val #[M, N, U] = Context.lookup H eq ^! EQ
      val #[] = U ^! BASE
      val z =
          case z of
              SOME z => z
            | NONE => Context.fresh (H, Variable.named "H")
    in
      [ MAIN |: H @@ (z, C.`> CEQUAL $$ #[M, N]) >> P
      ] BY (fn [D] => D.`> BASE_ELIM_EQ $$ #[z \\ D]
             | _ => raise Refine)
    end
end
