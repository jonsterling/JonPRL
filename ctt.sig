signature CTT =
sig
  type tactic
  type conv
  type name
  type term

  structure Development : DEVELOPMENT

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
    val UnitElim : name -> tactic

    (* H >> Ax = Ax ∈ Unit *)
    val AxEq : tactic

    (* H >> !A = !B ∈ U{k} by SquashEq
     * 1. H >> A = B ∈ U{k}
     *)
    val SquashEq : tactic

    (* H >> !A by SquashIntro
     * 1. H >> A
     *)
    val SquashIntro : tactic

    (* H, x : !A, H'[x] >> P[x] by SquashElim x
     * 1. H, x : !A, H'[Ax] >> P[Ax]
     *)
    val SquashElim : name -> tactic

    (* H >> (Σx:A)B[x] = (Σx:A')B'[x] ∈ U{k} by ProdEq z
     * 1. H >> A = A' ∈ U{k}
     * 2. H, z : A >> B[z] = B'[z] ∈ U{k}
     *)
    val ProdEq : name option -> tactic

    (* H >> (Σx:A)B[x] by ProdIntro M
     * 1. H >> M ∈ A
     * 2. H >> B[M]
     *)
    val ProdIntro : term -> tactic

    (* H, z : (Σx:A)B[x], H'[z] >> P[z] by ProdElim z (s, t)
     * H, z : (Σx:A)B[x], s : A, t : B[s], H'[<s,t>] >> P[<s,t>]
     *)
    val ProdElim : name -> (name * name) option -> tactic

    val PairEq : name option -> Level.t option -> tactic
    val SpreadEq : term option -> term option -> (name * name * name) option  -> tactic

    val FunEq : name option -> tactic
    val FunIntro : name option -> Level.t option -> tactic
    val FunElim : name -> term -> (name * name) option -> tactic
    val LamEq : name option -> Level.t option -> tactic
    val ApEq : term option -> tactic

    val IsectEq : name option -> tactic
    val IsectIntro : name option -> Level.t option -> tactic
    val IsectElim : name -> term -> (name * name) option -> tactic
    val IsectMemberEq : name option -> Level.t option -> tactic
    val IsectMemberCaseEq : term option -> term -> tactic

    val MemUnfold : tactic
    val Witness : term -> tactic

    val Assumption : tactic
    val Hypothesis : name -> tactic
    val HypEq : tactic

    val Lemma : Development.t * Development.label -> tactic

    val RewriteGoal : conv -> tactic

    val EqSubst : term -> term -> Level.t option -> tactic
    val EqSym : tactic
  end

  structure Conversions :
  sig
    val ApBeta : conv
    val SpreadBeta : conv
  end
end
