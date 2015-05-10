signature LIBRARY =
sig
  type t

  type goal
  type evidence
  type tactic

  val all : unit -> t list
  val name : t -> string
  val goal : t -> goal

  val save : string -> goal -> tactic -> t
  val validate : t -> evidence
end
