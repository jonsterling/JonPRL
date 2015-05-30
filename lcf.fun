functor Lcf
  (structure Sequent : SEQUENT
   type evidence) : LCF =
struct
  type goal = Sequent.sequent
  type evidence = evidence
  type validation = evidence list -> evidence
  type tactic = goal -> (goal list * validation)
  val goal_to_string = Sequent.to_string
end

structure Lcf = Lcf
  (structure Sequent = Sequent
   type evidence = Syntax.t)
