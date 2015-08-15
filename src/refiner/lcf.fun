functor Lcf
  (structure Sequent : SEQUENT
   type evidence) : LCF_APART =
struct
  type goal = Sequent.sequent Goal.goal
  type evidence = evidence
  type validation = evidence list -> evidence
  type tactic = goal -> (goal list * validation)
  val goalToString = Goal.toString Sequent.toString

  fun goalApart (Goal.|: (_, s1), Goal.|: (_, s2)) =
    not (Sequent.eq (s1, s2))
end

structure Lcf = Lcf
  (structure Sequent = Sequent
   type evidence = Syntax.t)

structure AnnotatedLcf = AnnotatedLcf
  (structure Lcf = Lcf
   type metadata = {name : string, pos : Pos.t})
