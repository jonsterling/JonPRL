signature REFINER_TYPES =
sig
  type goal
  type evidence

  type validation = evidence list -> evidence
  type tactic = goal -> goal list * validation

  val print_goal : goal -> string
end

