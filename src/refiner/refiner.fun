functor Refiner
  (structure Syntax : ABT_UTIL
     where type Operator.t = UniversalOperator.t
   structure Sequent : SEQUENT
     where type term = Syntax.t
     where Context.Syntax = Syntax
   structure Lcf : LCF
     where type evidence = Syntax.t
     where type goal = Sequent.sequent Goal.goal

   structure Development : DEVELOPMENT
     where type judgement = Sequent.sequent
     where type evidence = Lcf.evidence
     where type tactic = Lcf.tactic
     where type operator = UniversalOperator.t

   structure Conv : CONV where type term = Syntax.t
   structure Semantics : SMALL_STEP where type syn = Syntax.t
   sharing type Development.term = Syntax.t
   structure Builtins : BUILTINS
     where type Conv.term = Conv.term) : REFINER =
struct
  structure Lcf = Lcf
  structure Conv = ConvUtil(structure Conv = Conv and Syntax = Syntax)
  structure Syntax = Syntax

  structure Sequent = Sequent
  structure Development = Development

  type tactic = Lcf.tactic
  type conv = Conv.conv
  type name = Sequent.name
  type term = Syntax.t
  type goal = Sequent.sequent

  type operator = Syntax.Operator.t
  type hyp = name HypSyn.t

  type world = Development.world

  exception Refine

  structure Rules =
  struct
    structure Utils = RulesUtil
      (structure Lcf = Lcf
       structure Syntax = Syntax
       structure Conv = Conv
       structure Semantics = Semantics
       structure Sequent = Sequent
       structure Development = Development
       structure Builtins = Builtins

       exception Refine = Refine)

    open Utils
    open Goal Sequent Syntax CttCalculus Derivation

    infix $ \ BY ^!
    infix 3 >>
    infix 2 |:
    infix 8 $$ // @@
    infixr 8 \\

    structure UnivRules = UnivRules(Utils)
    open UnivRules

    structure EqRules = EqRules(Utils)
    open EqRules

    structure FunRules = FunRules(Utils)
    open FunRules

    structure ISectRules = ISectRules(Utils)
    open ISectRules

    structure SubsetRules = SubsetRules(Utils)
    open SubsetRules

    structure NatRules = NatRules(Utils)
    open NatRules

    structure BaseRules = BaseRules(Utils)
    open BaseRules

    structure ImageRules = ImageRules(Utils)
    open ImageRules

    structure GeneralRules = GeneralRules(Utils)
    open GeneralRules

    structure ProdRules = ProdRules(Utils)
    open ProdRules

    structure PlusRules = PlusRules(Utils)
    open PlusRules

    structure AtomRules = AtomRules(Utils)
    open AtomRules

    structure CEqRules = CEqRules(Utils)
    open CEqRules

    local
      open CttCalculusView
      datatype ForallType = ForallIsect | ForallFun
      structure Tacticals = Tacticals (Lcf)
      open Tacticals
      infix THEN THENL
    in
      fun stripForalls (H, P) =
        case project P of
             ISECT $ #[A, xB] =>
               let
                 val (H', x, B) = ctxUnbind (H, A, xB)
                 val (xs, Q) = stripForalls (H', B)
               in
                 (xs @ [(ForallIsect, x)], Q)
               end
           | FUN $ #[A, xB] =>
               let
                 val (H', x, B) = ctxUnbind (H, A, xB)
                 val (xs, Q) = stripForalls (H', B)
               in
                 (xs @ [(ForallFun, x)], Q)
               end
           | _ => ([], P)

      fun BHyp hyp (goal as _ |: (sequent as H >> P)) =
        let
          val target = eliminationTarget hyp sequent

          val (variables, Q) = stripForalls (H, Context.lookup H target)
          val fvs = List.map #1 (Context.listItems H)
          val solution = Unify.unify (Meta.convertFree fvs Q, Meta.convertFree fvs P)

          val instantiations = List.map (fn (ty, v) => (ty, Unify.Solution.lookup solution v)) variables

          val targetRef = ref target
          fun go [] = ID
            | go ((ty, e) :: es) = fn goal' as _ |: H' >> _ =>
              let
                val currentTarget = Context.rebindName H' (! targetRef)
                val nextTarget = Variable.prime currentTarget
                val _ = targetRef := nextTarget
                val instantiation = Meta.unconvert (fn _ => raise Refine) e
                val eqName = Context.fresh (H', Variable.named "_")
                val names = (nextTarget, eqName)
                val hyp = HypSyn.NAME currentTarget
                val elim =
                  case ty of
                       ForallIsect => IsectElim
                     | ForallFun => FunElim
                val tac =
                  elim (hyp, instantiation, SOME names)
                    THEN Thin hyp
              in
                (tac THENL [ID, go es]) goal'
              end
        in
          go (rev instantiations) goal
        end
    end

    local
      structure Tacticals = Tacticals (Lcf)
      open Tacticals
      infix THEN THENL
    in
      fun HypEqSubst (dir, hyp, xC, ok) (goal as _ |: H >> P) =
        let
          val z = eliminationTarget hyp (H >> P)
          val X = Context.lookup H z
        in
          case dir of
               Dir.RIGHT => (EqSubst (X, xC, ok) THENL [Hypothesis_ z, ID, ID]) goal
             | Dir.LEFT =>
                 let
                   val #[M,N,A] = X ^! EQ
                 in
                   (EqSubst (C.`> EQ $$ #[N,M,A], xC, ok)
                     THENL [EqSym THEN Hypothesis_ z, ID, ID]) goal
                 end
        end

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
  end

  structure Conversions =
  struct
    open Conv

    val Step : conv = fn M =>
      case Semantics.step M of
           Semantics.STEP M' => M'
         | _ => raise Conv
  end
end

structure Refiner = Refiner
  (structure Lcf = Lcf
   structure Syntax = Syntax
   structure Conv = Conv
   structure Semantics = Semantics
   structure Sequent = Sequent
   structure Development = Development
   structure Builtins = Builtins)
