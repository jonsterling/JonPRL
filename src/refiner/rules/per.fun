functor PerRules(Utils : RULES_UTIL) : PER_RULES =
struct
  open Utils
  open Goal Sequent Syntax CttCalculus Derivation

  infix $ \ BY ^!
  infix 3 >>
  infix 2 |:
  infix 8 $$ // @@
  infixr 8 \\

  local
    fun ap2 R u v = (R // u) // v
  in

    fun Eq ow (_ |: H >> P) =
      let
        val #[M, N, U] = P ^! EQ
        val #[R1] = M ^! PER
        val #[R2] = N ^! PER
        val (UNIV _, _) = asApp U
        val (x,y,z,u,v) =
         case ow of
             SOME names => names
           | NONE => (Context.fresh (H, Variable.named "x"),
                      Context.fresh (H, Variable.named "y"),
                      Context.fresh (H, Variable.named "z"),
                      Context.fresh (H, Variable.named "u"),
                      Context.fresh (H, Variable.named "v"))
        val bas = C.`> BASE $$ #[]
      in
        [ MAIN |: H @@ (x,bas) @@ (y,bas) >> C.`> MEM $$ #[ap2 R1 (``x) (``y), U]
        , MAIN |: H @@ (x,bas) @@ (y,bas) >> C.`> MEM $$ #[ap2 R2 (``x) (``y), U]
        , MAIN |: H @@ (x,bas) @@ (y,bas) @@ (z,ap2 R1 (``x) (``y)) >> ap2 R2 (``x) (``y)
        , MAIN |: H @@ (x,bas) @@ (y,bas) @@ (z,ap2 R2 (``x) (``y)) >> ap2 R1 (``x) (``y)
        , MAIN |: H @@ (x,bas) @@ (y,bas) @@ (z,ap2 R1 (``x) (``y)) >> ap2 R1 (``y) (``x)
        , MAIN |: H @@ (x,bas) @@ (y,bas) @@ (z,bas) @@ (u,ap2 R1 (``x) (``y)) @@ (v,ap2 R1 (``y) (``z)) >> ap2 R1 (``x) (``z)
        ] BY (fn [A,B,C,D,E,F] =>
                 D.`> PER_EQ $$ #[x \\ (y \\ A),
                                  x \\ (y \\ B),
                                  x \\ (y \\ (z \\ C)),
                                  x \\ (y \\ (z \\ D)),
                                  x \\ (y \\ (z \\ E)),
                                  x \\ (y \\ (z \\ (u \\ (v \\ F))))]
             | _ => raise Refine)
      end

    fun MemEq ok (_ |: H >> P) =
      let
        val #[M, N, U] = P ^! EQ
        val #[R] = U ^! PER
        val k = case ok of NONE => inferLevel (H, U) | SOME k => k
        val uni = C.`> (UNIV k) $$ #[]
        val bas = C.`> BASE $$ #[]
      in
        [ MAIN |: H >> C.`> MEM $$ #[U, uni]
        , MAIN |: H >> ap2 R M N
        , MAIN |: H >> C.`> MEM $$ #[M, bas]
        , MAIN |: H >> C.`> MEM $$ #[N, bas]
        ] BY mkEvidence PER_MEM_EQ
      end

    fun Elim (hyp, ow, ok) (_ |: H >> P) =
      let
        val z = eliminationTarget hyp (H >> P)
        val #[M,N,U] = Context.lookup H z ^! EQ
        val #[R] = U ^! PER
        val y =
         case ow of
             SOME names => names
           | NONE => Context.fresh (H, Variable.named "y")
        val k = case ok of NONE => inferLevel (H, U) | SOME k => k
        val uni = C.`> (UNIV k) $$ #[]
        val rmn = ap2 R M N
        val K  = Context.insert Context.empty y Visibility.Hidden rmn
        val H1 = Context.interposeAfter H (z, K)
      in
        [ MAIN |: H1 >> P
        , MAIN |: H >> C.`> MEM $$ #[rmn, uni]
        ] BY (fn [D,E] => D.`> PER_ELIM $$ #[y \\ D, E]
               | _ => raise Refine)
      end
  end
end
