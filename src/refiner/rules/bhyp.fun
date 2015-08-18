functor BHypRules
  (structure U : RULES_UTIL

   val FunElim : U.hyp * U.term * (U.name * U.name) option -> U.tactic
   val IsectElim : U.hyp * U.term * (U.name * U.name) option -> U.tactic
   val Thin : U.hyp -> U.tactic) :
   BHYP_RULES =
struct
  open U
  open Goal Sequent Syntax CttCalculus Derivation

  infix $ \ BY ^!
  infix 3 >>
  infix 2 |:
  infix 8 $$ // @@
  infixr 8 \\

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
end
