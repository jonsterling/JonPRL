functor ProdRules(Utils : RULES_UTIL) : PROD_RULES =
struct
  open Utils
  open Goal Sequent Syntax CttCalculus Derivation

  infix $ \ BY ^!
  infix 3 >>
  infix 2 |:
  infix 8 $$ // @@
  infixr 8 \\

  val Eq = QuantifierEq (PROD, PROD_EQ)

  fun Intro (w, oz, ok) (_ |: H >> P) =
    let
      val w = Context.rebind H w
      val #[P1, xP2] = P ^! PROD
      val k = case ok of SOME k => k | NONE => inferLevel (H, P)
      val z =
        Context.fresh (H,
          case oz of
               SOME z => z
             | NONE => #1 (unbind xP2))
    in
      [ AUX |: H >> C.`> MEM $$ #[w, P1]
      , MAIN |: H >> xP2 // w
      , AUX |: H @@ (z, P1) >> C.`> MEM $$ #[xP2 // ``z, C.`> (UNIV k) $$ #[]]
      ] BY (fn [D, E, F] => D.`> PROD_INTRO $$ #[w, D, E, z \\ F]
             | _ => raise Refine)
    end

  fun IndependentIntro (_ |: H >> P) =
    let
      val #[P1, xP2] = P ^! PROD
      val (x, P2) = unbind xP2
      val _ = if hasFree (P2, x) then raise Refine else ()
    in
      [ MAIN |: H >> P1
      , MAIN |: H >> P2
      ] BY mkEvidence IND_PROD_INTRO
    end

  fun Elim (hyp, onames) (_ |: H >> P) =
    let
      val z = eliminationTarget hyp (H >> P)
      val #[S, xT] = Context.lookup H z ^! PROD
      val (s, t) =
        case onames of
             SOME names => names
           | NONE =>
               (Context.fresh (H, Variable.named "s"),
                Context.fresh (H, Variable.named "t"))

      val st = C.`> PAIR $$ #[``s, ``t]
      val J = Context.empty @@ (s, S) @@ (t, (xT // ``s))
      val H' = ctxSubst (Context.interposeAfter H (z, J)) st z
    in
      [ MAIN |: H' >> subst st z P
      ] BY (fn [D] => D.`> PROD_ELIM $$ #[``z, s \\ (t \\ D)]
             | _ => raise Refine)
    end

  fun MemEq (oz, ok) (_ |: H >> P) =
    let
      val #[pair, pair', prod] = P ^! EQ
      val #[M, N] = pair ^! PAIR
      val #[M', N'] = pair' ^! PAIR
      val #[A, xB] = prod ^! PROD
      val z =
        Context.fresh (H,
          case oz of
               NONE => #1 (unbind xB)
             | SOME z => z)
      val k = case ok of NONE => inferLevel (H, A) | SOME k => k
    in
      [ MAIN |: H >> C.`> EQ $$ #[M, M', A]
      , MAIN |: H >> C.`> EQ $$ #[N, N', xB // M]
      , AUX |: H @@ (z,A) >> C.`> MEM $$ #[xB // `` z, C.`> (UNIV k) $$ #[]]
      ] BY (fn [D,E,F] => D.`> PAIR_EQ $$ #[D, E, z \\ F]
             | _ => raise Refine)
    end

  fun SpreadEq (ozC, oprod, onames) (_ |: H >> P) =
    let
      val #[spread, spread', CE1] = P ^! EQ
      val #[E1, xyT1] = spread ^! SPREAD
      val #[E2, uvT2] = spread' ^! SPREAD

      val prod =
        case oprod of
             NONE => typeLub H (inferType (H, E1)) (inferType (H, E2))
           | SOME prod => Context.rebind H prod

      val (s,t,y) =
        case onames of
             NONE =>
              (Context.fresh (H, Variable.named "s"),
               Context.fresh (H, Variable.named "t"),
               Context.fresh (H, Variable.named "y"))
           | SOME names => names

      val #[S, xT] = prod ^! PROD

      val z = Context.fresh (H, Variable.named "z")
      val zC =
        (case ozC of
             NONE =>
             let
               val H' = H @@ (z, prod)
               val Cz =
                 typeLub H'
                   (inferType (H', C.`> SPREAD $$ #[``z, xyT1]))
                   (inferType (H', C.`> SPREAD $$ #[``z, uvT2]))
             in
               z \\ Cz
             end
           | SOME zC => Context.rebind H zC)
        handle _ => z \\ CE1

      val CE1' = unify CE1 (zC // E1) handle _ => CE1
      val Ts = xT // ``s
      val st = C.`> PAIR $$ #[``s, ``t]
      val E1pair = C.`> EQ $$ #[E1, st, prod]
      val Cst = zC // st
      val T1st = (xyT1 // ``s) // ``t
      val T2st = (uvT2 // ``s) // ``t
    in
      [ MAIN |: H >> C.`> EQ $$ #[E1, E2, prod]
      , MAIN |: H @@ (s, S) @@ (t, Ts) @@ (y, E1pair) >> C.`> EQ $$ #[T1st, T2st, Cst]
      ] BY (fn [D, E] => D.`> SPREAD_EQ $$ #[D, s \\ (t \\ (y \\ E))]
              | _ => raise Refine)
    end
end
