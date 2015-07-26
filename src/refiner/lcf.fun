functor Lcf
  (structure Sequent : SEQUENT
   type evidence) : LCF_APART =
struct
  type goal = Sequent.sequent
  type evidence = evidence
  type validation = evidence list -> evidence
  type tactic = goal -> (goal list * validation)
  val goalToString = Sequent.toString
  val goalApart = not o Sequent.eq
end

structure Lcf = Lcf
  (structure Sequent = Sequent
   type evidence = Syntax.t)

structure AnnotatedLcf = AnnotatedLcf
  (structure Lcf = Lcf
   type metadata = {name : string, pos : Pos.t})
