functor RefinerTypes
  (structure Sequent : SEQUENT
   type evidence) : REFINER_TYPES =
struct
  type goal = Sequent.sequent
  type evidence = evidence
  type validation = evidence list -> evidence
  type tactic = goal -> (goal list * validation)
  val goal_to_string = Sequent.to_string
end

