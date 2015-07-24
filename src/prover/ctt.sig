signature CTT =
sig
  type name
  type term

  type conv
  type world
  type tactic

  exception Refine

  structure Sequent : SEQUENT
    where type term = term

  structure Development : DEVELOPMENT
    where type tactic = tactic
    where type world = world
    where type judgement = Sequent.sequent

  type label = Development.label

  type hyp = name HypSyn.t

  structure Rules : sig
    (* Pretend you have got a proof. *)
    val Admit : tactic

    (* H >> A = B ∈ U{l} by Cum k (k < l)
     * 1.  H >> A = B ∈ U{k}
     *)
    val Cum : Level.t option -> tactic

    (* H >> U{l} = U{l} ∈ U{k} by UnivEq (l < k) *)
    val UnivEq : tactic

    (* H >> Void = Void ∈ U{k} by VoidEq *)
    val VoidEq : tactic

    (* H >> (M = N ∈ A) = (M' = N' ∈ A') ∈ U{k}
     * 1. H >> A = A' ∈ U{k}
     * 2. H >> M = M' ∈ A
     * 3. H >> N = N' ∈ A *)
    val EqEq : tactic

    (* H >> A by VoidElim
     * 1. H >> Void
     *)
    val VoidElim : tactic

    (* H >> Unit = Unit ∈ U{k} by UnitEq *)
    val UnitEq : tactic

    (* H >> Unit by UnitIntro *)
    val UnitIntro : tactic

    (* H, x : Unit, H'[x] >> P by UnitElim x
     * 1. H, x : Unit, H'[Ax] >> P[Ax]
     *)
    val UnitElim : hyp -> tactic

    (* H >> Ax = Ax ∈ Unit *)
    val AxEq : tactic

    (* H >> (Σx:A)B[x] = (Σx:A')B'[x] ∈ U{k} by ProdEq z
     * 1. H >> A = A' ∈ U{k}
     * 2. H, z : A >> B[z] = B'[z] ∈ U{k}
     *)
    val ProdEq : name option -> tactic

    (* H >> (Σx:A)B[x] by ProdIntro M
     * 1. H >> M ∈ A
     * 2. H >> B[M]
     * 3. H, x:A >> B[x] ∈ U{k}
     *)
    val ProdIntro : term * name option * Level.t option -> tactic
    val IndependentProdIntro : tactic

    (* H, z : (Σx:A)B[x], H'[z] >> P[z] by ProdElim z (s, t)
     * H, z : (Σx:A)B[x], s : A, t : B[s], H'[<s,t>] >> P[<s,t>]
     *)
    val ProdElim : hyp * (name * name) option -> tactic

    val PairEq : name option * Level.t option -> tactic
    val SpreadEq : term option * term option * (name * name * name) option -> tactic

    (* H >> A + B = A' + B' ∈ U{k}
     *   H >> A' = A' ∈ U{k}
     *   H >> B' = B' ∈ U{k}
     *)
    val PlusEq : tactic

    (* H >> inl X ∈ A + B
     *  H >> X ∈ A
     *  H >> B ∈ U{k}
     *)
    val PlusIntroL : Level.t option -> tactic

    (* H >> inl X ∈ A + B
     *  H >> X ∈ B
     *  H >> A ∈ U{k}
     *)
    val PlusIntroR : Level.t option -> tactic

    (* H, x : A + B >> C
     *   H, x : A + B, y : A >> C
     *   H, x : A + B, z : B >> C
     *)
    val PlusElim : (hyp * (name * name) option) -> tactic

    (* H >> inl X = inl Y ∈ A + B
     *    H >> X = Y ∈ A
     *    H >> B ∈ U{k}
     *)
    val InlEq : Level.t option -> tactic

    (* H >> inr X = inr Y ∈ A + B
     *    H >> X = Y ∈ B
     *    H >> A ∈ U{k}
     *)
    val InrEq : Level.t option -> tactic
    val DecideEq : term
                   -> (term * term * (name * name * name) option)
                   -> tactic

    val FunEq : name option -> tactic
    val FunIntro : name option * Level.t option -> tactic
    val FunElim : hyp * term * (name * name) option -> tactic
    val LamEq : name option * Level.t option -> tactic
    val ApEq : term option -> tactic
    val FunExt : name option * Level.t option -> tactic

    val IsectEq : name option -> tactic
    val IsectIntro : name option * Level.t option -> tactic
    val IsectElim : hyp * term * (name * name) option -> tactic
    val IsectMemberEq : name option * Level.t option -> tactic
    val IsectMemberCaseEq : term option * term -> tactic

    val SubsetEq : name option -> tactic
    val SubsetIntro : term * name option * Level.t option -> tactic
    val IndependentSubsetIntro : tactic
    val SubsetElim : hyp * (name * name) option -> tactic
    val SubsetMemberEq : name option * Level.t option -> tactic

    (* H >> nat = nat ∈ U{k} *)
    val NatEq : tactic

    (* H, z : nat, H' >> C[z]
     *   H, z : nat, H' >> C[0]
     *   H, z : nat, i : nat, p : C[i], H' >> C[s(i)]
     *)
    val NatElim : hyp * (name * name) option -> tactic

    val ZeroEq : tactic
    val SuccEq : tactic
    val NatRecEq : term option * (name * name) option -> tactic

    val BaseEq : tactic
    val BaseIntro : tactic
    val BaseMemberEq : tactic
    val BaseElimEq : hyp * name option -> tactic

    val Witness : term -> tactic

    val Assumption : tactic
    val Assert : term * name option -> tactic
    val Hypothesis : hyp -> tactic
    val HypEq : tactic
    val EqInSupertype : tactic

    val Unfolds : world * (label * Level.t option) list -> tactic
    val Lemma : world * label -> tactic

    val RewriteGoal : conv -> tactic

    val EqSubst : term * term * Level.t option -> tactic
    val EqSym : tactic

    val CEqEq       : tactic
    val CEqSym      : tactic
    val CEqStep     : tactic
    val CEqSubst    : term * term -> tactic
    val HypCEqSubst : Dir.dir * hyp * term -> tactic
    val CEqStruct   : tactic
    val CEqApprox   : tactic

    val ApproxEq    : tactic
    val ApproxExtEq : tactic
    val ApproxRefl  : tactic

    val BottomDiverges : hyp -> tactic

    val ImageEq    : tactic
    val ImageMemEq : tactic
    val ImageElim  : hyp * name option -> tactic
    val ImageEqInd : hyp * (name * name * name * name) option -> tactic

    val HypEqSubst : Dir.dir * hyp * term * Level.t option -> tactic

    (* Match a single branch of a [match goal]. This needs to
     * be primitive because it needs access to the structure of
     * the sequent. It doesn't construct it's own validations
     * though. Perhaps we should move this out to ctt_util.
     *)
    val MatchSingle : (name * term) list * term * ((name * term) list -> tactic)
                      -> tactic
  end

  structure Conversions :
  sig
    val Step : conv
  end
end
