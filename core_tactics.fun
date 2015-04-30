functor CoreTactics (R : REFINER_TYPES) :
  CORE_TACTICS where type tactic = R.tactic =
struct
  type tactic = R.tactic

  fun THEN (tac1, tac2) (g : R.goal) =
    let
      val (subgoals1, validation1) = tac1 g
      val (subgoals2, validations2) = ListPair.unzip (List.map tac2 subgoals1)
    in
      (List.foldl (op @) [] subgoals2,
       fn Ds =>
         let
           val lengths = List.map List.length subgoals2
           val derivations = ListUtil.multisplit lengths Ds
         in
           validation1 (ListPair.map (fn (v, d) => v d) (validations2, derivations))
         end)
    end

  fun ORELSE (tac1, tac2) : R.tactic = fn g =>
    tac1 g handle _ => tac2 g
end

