functor NeighborhoodRules(Utils : RULES_UTIL) : NEIGHBORHOOD_RULES =
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
      val #[neigh1, neigh2, univ] = P ^! EQ
      val (UNIV i, _) = asApp univ
      val #[F] = neigh1 ^! NEIGH
      val #[G] = neigh2 ^! NEIGH
    in
      [ MAIN |: H >> C.`> EQ $$ #[F, G, C.`> (CONTAINER i) $$ #[]]
      ] BY mkEvidence NEIGH_EQ
    end


  fun NilEq k (_ |: H >> P) =
    let
      val #[Nil1, Nil2, neigh] = P ^! EQ
      val #[F] = neigh ^! NEIGH
      val #[] = Nil1 ^! NEIGH_NIL
      val #[] = Nil2 ^! NEIGH_NIL
    in
      [ AUX |: H >> C.`> MEM $$ #[F, C.`> (CONTAINER k) $$ #[]]
      ] BY mkEvidence NEIGH_NIL_EQ
    end

  fun SnocEq k (_ |: H >> P) =
    let
      val #[ext1, ext2, neigh] = P ^! EQ
      val #[F] = neigh ^! NEIGH
      val #[U, rE] = ext1 ^! EXTEND
      val #[U', rE'] = ext2 ^! EXTEND
      val (H', r, E) = ctxUnbind (H, C.`> REFINEMENT $$ #[F, U], rE)
      val E'= rE' // ``r
    in
      [ MAIN |: H >> C.`> EQ $$ #[U, U', neigh]
      , MAIN |: H' >> C.`> EQ $$ #[E, E', C.`> DOM $$ #[F]]
      ] BY (fn [D, E] => D.`> NEIGH_SNOC_EQ $$ #[D, r \\ E]
             | _ => raise Refine)
    end

  structure Tacticals = Tacticals (Lcf)
  open Tacticals infix ORELSE

  fun MemEq ok (goal as _ |: H >> P) =
    let
      val #[_, _, neigh] = P ^! EQ
      val #[F] = neigh ^! NEIGH
      val k = case ok of SOME k => k | NONE => inferLevel (H, F)
    in
      (NilEq k ORELSE SnocEq k) goal
    end

  fun Elim (hyp, onames) (_ |: H >> C) =
    let
      val z = eliminationTarget hyp (H >> C)
      val #[F] = Context.lookup H z ^! NEIGH
      val (u,e,ih) =
        case onames of
             SOME names => names
           | NONE =>
               (Context.fresh (H, Variable.named "u"),
                Context.fresh (H, Variable.named "e"),
                Context.fresh (H, Variable.named "ih"))

      val r = Context.fresh (H, Variable.named "r")
      val Nil = C.`> NEIGH_NIL $$ #[]
      val snocu = C.`> EXTEND $$ #[``u, r \\ (C.`> AP $$ #[``e,``r])]

      val J =
        Context.empty
          @@ (u, C.`> NEIGH $$ #[F])
          @@ (e, C.`> FUN $$ #[C.`> REFINEMENT $$ #[F, ``u], r \\ (C.`> DOM $$ #[F])])
          @@ (ih, subst (``u) z C)

      val H' = Context.mapAfter u (Syntax.subst snocu z) (Context.interposeAfter H (z, J))
    in
      [ MAIN |: ctxSubst H Nil z >> subst Nil z C
      , MAIN |: H' >> subst snocu z C
      ] BY (fn [D,E] => D.`> NEIGH_ELIM $$ #[``z, D, u \\ (e \\ (ih \\ E))]
             | _ => raise Refine)
    end

  fun IndEq (ozC, oF, onames) (_ |: H >> P) =
    let
      val #[ind1, ind2, A] = P ^! EQ
      val #[N, nilCase, snocCase] = ind1 ^! NEIGH_IND
      val #[N', nilCase', snocCase'] = ind1 ^! NEIGH_IND

      val F =
        case oF of
             NONE =>
             let
               val #[F] = typeLub H (inferType (H, N)) (inferType (H, N')) ^! NEIGH
             in
               F
             end
           | SOME F=> Context.rebind H F

      val neigh = C.`> NEIGH $$ #[F]

      val zC =
        (case ozC of
             NONE =>
             let
               val z = Context.fresh (H, Variable.named "z")
               val H' = H @@ (z, neigh)
               val Cz =
                 typeLub H'
                   (inferType (H', C.`> NEIGH_IND $$ #[``z, nilCase, snocCase]))
                   (inferType (H', C.`> NEIGH_IND $$ #[``z, nilCase', snocCase']))
             in
               z \\ Cz
             end
           | SOME zC => Context.rebind H zC)
        handle _ => Variable.named "z" \\ A

      val (u,e,ih) =
        case onames of
             SOME names => names
           | NONE =>
               (Context.fresh (H, Variable.named "u"),
                Context.fresh (H, Variable.named "e"),
                Context.fresh (H, Variable.named "ih"))

      val r = Context.fresh (H, Variable.named "r")
      val neigh = C.`> NEIGH $$ #[F]
      val H' =
        H @@ (u, neigh)
          @@ (e, C.`> FUN $$ #[C.`> REFINEMENT $$ #[F, ``u], r \\ (C.`> DOM $$ #[F])])
          @@ (ih, zC // ``u)

      val snocSubst = (snocCase // ``u) // ``e // ``ih
      val snocSubst' = (snocCase' // ``u) // ``e // ``ih
      val snocu = C.`> EXTEND $$ #[``u, r \\ (C.`> AP $$ #[``e,``r])]
    in
      [ MAIN |: H >> C.`> EQ $$ #[N, N', neigh]
      , MAIN |: H >> C.`> EQ $$ #[nilCase, nilCase', zC // (C.`> NEIGH_NIL $$ #[])]
      , MAIN |: H' >> C.`> EQ $$ #[snocSubst, snocSubst', zC // snocu]
      ] BY (fn [N, D, E] => D.`> NEIGH_IND_EQ $$ #[N, D, u \\ e \\ ih \\ E]
             | _ => raise Refine)
    end
end

