functor ImageRules(Utils : RULES_UTIL) : IMAGE_RULES =
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
      val #[A1,f1] = M ^! IMAGE
      val #[A2,f2] = N ^! IMAGE
      val (UNIV _, _) = asApp U
    in
      [ MAIN |: H >> C.`> EQ $$ #[f1, f2, C.`> BASE $$ #[]]
      , MAIN |: H >> C.`> EQ $$ #[A1, A2, U]
      ] BY mkEvidence IMAGE_EQ
    end

  fun MemEq (_ |: H >> P) =
    let
      val #[M, N, U] = P ^! EQ
      val #[f1,a1] = M ^! AP
      val #[f2,a2] = N ^! AP
      val #[A,f] = U ^! IMAGE
      val true = Syntax.eq (f,f1)
      val true = Syntax.eq (f,f2)
    in
      [ MAIN |: H >> C.`> EQ $$ #[a1, a2, A]
      , MAIN |: H >> C.`> EQ $$ #[f, f, C.`> BASE $$ #[]]
      ] BY mkEvidence IMAGE_MEM_EQ
    end

  fun Elim (hyp, ow) (_ |: H >> P) =
    let
      val z = eliminationTarget hyp (H >> P)
      val #[A,F] = Context.lookup H z ^! IMAGE
      val w =
       case ow of
           SOME w => w
         | NONE => Context.fresh (H, Variable.named "w")

      val K  = Context.insert Context.empty w Visibility.Hidden A
      val H1 = Context.interposeAfter H (z, K)

      val Fw = C.`> AP $$ #[F, ``w]
      val H2 = Context.mapAfter w (fn t => subst Fw z t) H1
      val P' = subst Fw z P
    in
      [ MAIN |: H2 >> P'
      ] BY (fn [D] => D.`> IMAGE_ELIM $$ #[w \\ D]
             | _ => raise Refine)
    end

  fun EqInd (hyp, onames) (_ |: H >> P) =
    let
      val x = eliminationTarget hyp (H >> P)
      val #[T2',AP1,U] = Context.lookup H x ^! EQ
      val (a,b,y,z) =
        case onames of
             SOME names => names
           | NONE => (Context.fresh (H, Variable.named "a"),
           Context.fresh (H, Variable.named "b"),
           Context.fresh (H, Variable.named "y"),
           Context.fresh (H, Variable.named "z"))
      val #[A,f] = U ^! IMAGE
      val #[T2, AP2, T] = P ^! EQ
      val #[F,T1] = AP1 ^! AP
      val #[F',T1'] = AP2 ^! AP
      val true = Syntax.eq (T2,T2')
      val true = Syntax.eq (F,F')
      val true = Syntax.eq (T1,T1')
      val base = C.`> BASE $$ #[]
      val fa = C.`> AP $$ #[F,``a]
      val fb = C.`> AP $$ #[F,``b]
    in
      [ MAIN |: H >> C.`> EQ $$ #[F, F, base]
      , MAIN |: H >> C.`> EQ $$ #[T1, T1, A]
      , MAIN |: H >> C.`> EQ $$ #[AP1, AP1, T]
      , MAIN |: H @@ (a,base) @@ (b,base) @@ (y, C.`> EQ $$ #[fa,fa,T]) @@ (z, C.`> EQ $$ #[``a,``b,A]) >> C.`> EQ $$ #[fa,fb,T]
      ] BY (fn [D1,D2,D3,D4] => D.`> IMAGE_EQ_IND $$ #[D1,D2,D3, a \\ b \\ y \\ z \\ D4]
             | _ => raise Refine)
    end


end
