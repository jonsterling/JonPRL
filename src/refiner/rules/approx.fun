functor ApproxRules(Utils : RULES_UTIL) : APPROX_RULES =
struct
  open Utils
  open Goal Sequent Syntax CttCalculus Derivation

  infix $ \ BY ^!
  infix 3 >>
  infix 2 |:
  infix 8 $$ // @@
  infixr 8 \\

  fun ApproxEq (_ |: H >> P) =
    let
      val #[approx1, approx2, univ] = P ^! EQ
      val (UNIV _, _) = asApp univ
      val #[M,N] = approx1 ^! APPROX
      val #[M',N'] = approx2 ^! APPROX
      val base = C.`> BASE $$ #[]
    in
      [ MAIN |: H >> C.`> EQ $$ #[M,M',base]
      , MAIN |: H >> C.`> EQ $$ #[N,N',base]
      ] BY mkEvidence APPROX_EQ
    end

  fun ApproxMemEq (_ |: H >> P) =
    let
      val #[M, N, E] = P ^! EQ
      val #[] = M ^! AX
      val #[] = N ^! AX
      val #[_, _] = E ^! APPROX
    in
      [ MAIN |: H >> E
      ] BY mkEvidence APPROX_MEMBER_EQ
    end

  fun ApproxExtEq (_ |: H >> P) =
    let
      val #[approx1, approx2, univ] = P ^! EQ
      val (UNIV _, _) = asApp univ
      val #[_,_] = approx1 ^! APPROX
      val #[_,_] = approx2 ^! APPROX
      val iff = C.`> IFF $$ #[approx1, approx2]
      val squ = C.`> SQUASH $$ #[iff]
    in
      [ MAIN |: H >> squ
      ] BY mkEvidence APPROX_EXT_EQ
    end

  local
    fun bothStuck M N =
      (Semantics.step M; raise Refine)
      handle Semantics.Stuck _ =>
        (Semantics.step N; raise Refine)
           handle Semantics.Stuck _ => ()
  in
    fun ApproxRefl (_ |: H >> P) =
      let
        val #[M, N] = P ^! APPROX
        val () = (unify M N; ()) handle Refine => bothStuck M N
      in
        [] BY mkEvidence APPROX_REFL
      end
  end

  fun ApproxElim hyp (goal as _ |: (sequent as H >> P)) =
    let
      val z = eliminationTarget hyp sequent
      val _ = Context.lookup H z ^! APPROX
      val ax = C.`> AX $$ #[]
      val H' = ctxSubst H ax z
      val P' = subst ax z P
    in
      [ MAIN |: H' >> P'
      ] BY (fn [D] => D.`> APPROX_ELIM $$ #[`` z, D]
             | _ => raise Refine)
    end

  fun AssumeHasValue (onames, ok) (_ |: H >> P) =
    let
      val #[M,N] = P ^! APPROX
      val y =
        case onames of
             SOME names => names
           | NONE => Context.fresh (H, Variable.named "y")
      val hv = C.`> HASVALUE $$ #[M]
      val k = case ok of SOME k => k | NONE => inferLevel (H, hv)
      val uni = C.`> (UNIV k) $$ #[]
      val mem = C.`> MEM $$ #[hv, uni]
    in
      [ MAIN |: H @@ (y, hv) >> P
      , AUX |: H >> mem
      ] BY (fn [A,B] => D.`> ASSUME_HAS_VALUE $$ #[y \\ A,B]
             | _ => raise Refine)
    end

  fun BottomDiverges hyp (_ |: H >> P) =
    let
      val x = eliminationTarget hyp (H >> P)
      val h = Context.lookup H x
      val #[M] = h ^! HASVALUE
      val #[] = M ^! BOT
    in
      [] BY (fn _ => D.`> BOTTOM_DIVERGES $$ #[``x])
    end
end
