signature CTT =
sig
  structure Syntax : ABT
  type name = Syntax.Variable.t
  type term = Syntax.t

  structure Lcf : LCF
  structure ConvTypes : CONV_TYPES
  sharing ConvTypes.Syntax = Syntax

  structure Development : DEVELOPMENT
  sharing Development.Telescope.Label = Syntax.Variable
  sharing Development.Lcf = Lcf

  structure Rules : sig
    (* Pretend you have got a proof. *)
    val Admit : Lcf.tactic

    (* H >> A = B ∈ U{l} by Cum k (k < l)
     * 1.  H >> A = B ∈ U{k}
     *)
    val Cum : Level.t option -> Lcf.tactic

    (* H >> U{l} = U{l} ∈ U{k} by UnivEq (l < k) *)
    val UnivEq : Lcf.tactic

    (* H >> Void = Void ∈ U{k} by VoidEq *)
    val VoidEq : Lcf.tactic

    (* H >> (M = N ∈ A) = (M' = N' ∈ A') ∈ U{k}
     * 1. H >> A = A' ∈ U{k}
     * 2. H >> M = M' ∈ A
     * 3. H >> N = N' ∈ A *)
    val EqEq : Lcf.tactic

    (* H >> A by VoidElim
     * 1. H >> Void
     *)
    val VoidElim : Lcf.tactic

    (* H >> Unit = Unit ∈ U{k} by UnitEq *)
    val UnitEq : Lcf.tactic

    (* H >> Unit by UnitIntro *)
    val UnitIntro : Lcf.tactic

    (* H, x : Unit, H'[x] >> P by UnitElim x
     * 1. H, x : Unit, H'[Ax] >> P[Ax]
     *)
    val UnitElim : name -> Lcf.tactic

    (* H >> Ax = Ax ∈ Unit *)
    val AxEq : Lcf.tactic

    (* H >> !A = !B ∈ U{k} by SquashEq
     * 1. H >> A = B ∈ U{k}
     *)
    val SquashEq : Lcf.tactic

    (* H >> !A by SquashIntro
     * 1. H >> A
     *)
    val SquashIntro : Lcf.tactic

    (* H, x : !A, H'[x] >> P[x] by SquashElim x
     * 1. H, x : !A, H'[Ax] >> P[Ax]
     *)
    val SquashElim : name -> Lcf.tactic

    (* H >> (Σx:A)B[x] = (Σx:A')B'[x] ∈ U{k} by ProdEq z
     * 1. H >> A = A' ∈ U{k}
     * 2. H, z : A >> B[z] = B'[z] ∈ U{k}
     *)
    val ProdEq : name option -> Lcf.tactic

    (* H >> (Σx:A)B[x] by ProdIntro M
     * 1. H >> M ∈ A
     * 2. H >> B[M]
     *)
    val ProdIntro : term -> Lcf.tactic

    (* H, z : (Σx:A)B[x], H'[z] >> P[z] by ProdElim z (s, t)
     * H, z : (Σx:A)B[x], s : A, t : B[s], H'[<s,t>] >> P[<s,t>]
     *)
    val ProdElim : name -> (name * name) option -> Lcf.tactic

    val PairEq : name option -> Level.t option -> Lcf.tactic
    val SpreadEq : term option -> term option -> (name * name * name) option  -> Lcf.tactic

    val FunEq : name option -> Lcf.tactic
    val FunIntro : name option -> Level.t option -> Lcf.tactic
    val FunElim : name -> term -> (name * name) option -> Lcf.tactic
    val LamEq : name option -> Level.t option -> Lcf.tactic
    val ApEq : term option -> Lcf.tactic

    val IsectEq : name option -> Lcf.tactic
    val IsectIntro : name option -> Level.t option -> Lcf.tactic
    val IsectElim : name -> term -> (name * name) option -> Lcf.tactic
    val IsectMemberEq : name option -> Level.t option -> Lcf.tactic
    val IsectMemberCaseEq : term option -> term -> Lcf.tactic

    val MemUnfold : Lcf.tactic
    val Witness : term -> Lcf.tactic

    val Assumption : Lcf.tactic
    val Hypothesis : name -> Lcf.tactic
    val HypEq : Lcf.tactic

    val Unfold : Development.t * Development.label -> Lcf.tactic
    val Lemma : Development.t * Development.label -> Lcf.tactic

    val RewriteGoal : ConvTypes.conv -> Lcf.tactic

    val EqSubst : term -> term -> Level.t option -> Lcf.tactic
    val EqSym : Lcf.tactic
  end

  structure Conversions :
  sig
    val ApBeta : ConvTypes.conv
    val SpreadBeta : ConvTypes.conv
  end
end
