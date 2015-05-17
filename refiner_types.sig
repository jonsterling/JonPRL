signature REFINER_TYPES =
sig
  type goal
  type evidence

  type validation = evidence list -> evidence
  type tactic = goal -> goal list * validation

  val goal_to_string : PrintMode.t -> goal -> string
end

