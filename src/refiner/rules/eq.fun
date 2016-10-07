functor EqRules(Utils : RULES_UTIL) : EQ_RULES =
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

  fun EqBase (_ |: H >> P) =
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

  fun MemEq (_ |: H >> P) =
    let
      val #[M, N, E] = P ^! EQ
      val #[] = M ^! AX
      val #[] = N ^! AX
      val #[M', N', T] = E ^! EQ
    in
      [ MAIN |: H >> E
      ] BY mkEvidence EQ_MEMBER_EQ
    end

  fun Sym (_ |: H >> P) =
    let
      val #[M,N,A] = P ^! EQ
    in
      [ MAIN |: H >> C.`> EQ $$ #[N,M,A]
      ] BY mkEvidence EQ_SYM
    end

  fun Subst (eq, xC, ok) (_ |: H >> P) =
    let
      val eq = Context.rebind H eq
      val #[M,N,A] = eq ^! EQ
      val xC = Context.rebind H xC

      val meta = convertToPattern (H, xC // M)
      val solution = Unify.unify (meta, Meta.convert P)

      val x \ C = out xC
      val xC = x \\ applySolution solution (P, convertToPattern (H, C))

      val (H', x, C) = ctxUnbind (H, A, xC)
      val k = case ok of SOME k => k | NONE => inferLevel (H', C)
    in
      [ AUX |: H >> eq
      , MAIN |: H >> xC // N
      , AUX |: H' >> C.`> MEM $$ #[C, C.`> (UNIV k) $$ #[]]
      ] BY (fn [D,E,F] => D.`> EQ_SUBST $$ #[D, E, x \\ F]
             | _ => raise Refine)
    end

  local
    structure Tacticals = Tacticals (Lcf)
    open Tacticals
    infix THEN THENL
  in
    fun HypSubst (dir, hyp, xC, ok) (goal as _ |: H >> P) =
      let
        val z = eliminationTarget hyp (H >> P)
        val X = Context.lookup H z
      in
        case dir of
             Dir.RIGHT => (Subst (X, xC, ok) THENL [Hypothesis_ z, ID, ID]) goal
           | Dir.LEFT =>
               let
                 val #[M,N,A] = X ^! EQ
               in
                 (Subst (C.`> EQ $$ #[N,M,A], xC, ok)
                   THENL [Sym THEN Hypothesis_ z, ID, ID]) goal
               end
      end
  end
end
