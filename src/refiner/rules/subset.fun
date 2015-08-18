functor SubsetRules(Utils : RULES_UTIL) : SUBSET_RULES =
struct
  open Utils
  open Goal Sequent Syntax CttCalculus Derivation

  infix $ \ BY ^!
  infix 3 >>
  infix 2 |:
  infix 8 $$ // @@
  infixr 8 \\

  val Eq = QuantifierEq (SUBSET, SUBSET_EQ)

  fun Intro (w, oz, ok) (_ |: H >> P) =
    let
      val w = Context.rebind H w
      val #[P1, xP2] = P ^! SUBSET
      val k = case ok of SOME k => k | NONE => inferLevel (H, P)
      val z =
        Context.fresh (H,
          case oz of
               SOME z => z
             | NONE => #1 (unbind xP2))
    in
      [ AUX |: H >> C.`> MEM $$ #[ w, P1]
      , MAIN |: H >> xP2 // w
      , AUX |: H @@ (z, P1) >> C.`> MEM $$ #[xP2 // ``z, C.`> (UNIV k) $$ #[]]
      ] BY (fn [D, E, F] => D.`> SUBSET_INTRO $$ #[w, D, E, z \\ F]
             | _ => raise Refine)
    end

  fun IndependentIntro (_ |: H >> P) =
    let
      val #[P1, xP2] = P ^! SUBSET
      val (x, P2) = unbind xP2
      val _ = if hasFree (P2, x) then raise Refine else ()
    in
      [ MAIN |: H >> P1
      , MAIN |: H >> P2
      ] BY mkEvidence IND_SUBSET_INTRO
    end

  fun SubsetElim_ (z : Sequent.name, onames) (_ |: H >> P) =
    let
      val #[S, xT] = Context.lookup H z ^! SUBSET
      val (s, t) =
        case onames of
             SOME names => names
           | NONE =>
               (Context.fresh (H, #1 (unbind xT)),
                Context.fresh (H, Variable.named "t"))

      val G = Context.empty @@ (s, S)
      val G' = Context.insert G t Visibility.Hidden (xT // ``s)
      val H' = ctxSubst (Context.interposeAfter H (z, G')) (``s) z
      val P' = subst (``s) z P
    in
      [ MAIN |: H' >> P'
      ] BY (fn [D] => D.`> SUBSET_ELIM $$ #[``z, s \\ (t \\ D)]
             | _ => raise Refine)
    end

  fun Elim (hyp, onames) (goal as _ |: sequent) =
    SubsetElim_ (eliminationTarget hyp sequent, onames) goal

  fun MemberEq (oz, ok) (_ |: H >> P) =
    let
      val #[s,t,subset] = P ^! EQ
      val #[S,xT] = subset ^! SUBSET
      val z =
        Context.fresh (H,
          case oz of
               NONE => #1 (unbind xT)
             | SOME z => z)
      val k = case ok of SOME k => k | NONE => inferLevel (H, subset)
    in
      [ MAIN |: H >> C.`> EQ $$ #[s,t,S]
      , MAIN |: H >> xT // s
      , AUX |: H @@ (z,S) >> C.`> MEM $$ #[xT // ``z, C.`> (UNIV k) $$ #[]]
      ] BY (fn [D, E, F] => D.`> SUBSET_MEMBER_EQ $$ #[D, E, z \\ F]
             | _ => raise Refine)
    end

  local
    structure Tacticals = Tacticals(Lcf)
    open Tacticals CttCalculusView infix THEN

    fun HypEq (_ |: H >> P) =
      let
        val P = P
        val #[M, M', A] = P ^! EQ
        val x = asVariable (unify M M')
        val _ = unify A (Context.lookup H x)
      in
        [] BY (fn _ => D.`> HYP_EQ $$ #[`` x])
      end
  in
    fun EqInSupertype (goal as _ |: H >> P) =
      let
        val #[M,N,A] = P ^! EQ
        val result =
          Context.search H (fn A' =>
            case project A' of
                 SUBSET $ #[A'', _] => Syntax.eq (A, A'')
               | _ => false)
        val x = case result of SOME (x,_) => x | NONE => raise Refine
      in
        (SubsetElim_ (x, NONE) THEN HypEq) goal
      end
  end
end
