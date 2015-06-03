functor Lcf
  (structure Sequent : SEQUENT
   type evidence) : LCF_APART =
struct
  type goal = Sequent.sequent
  type evidence = evidence
  type validation = evidence list -> evidence
  type tactic = goal -> (goal list * validation)
  val goal_to_string = Sequent.to_string
  val goal_apart = not o Sequent.eq
end

structure Lcf = Lcf
  (structure Sequent = Sequent
   type evidence = Syntax.t)
