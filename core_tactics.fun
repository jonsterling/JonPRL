functor CoreTactics (R : REFINER_TYPES) :
  CORE_TACTICS where type tactic = R.tactic =
struct
  type tactic = R.tactic

  fun ID g =
    ([g], fn [D] => D | _ => raise Fail "ID")

  local
    fun refine (supervalidation, subgoals, validations) =
      (List.foldl (op @) [] subgoals,
       fn Ds =>
         let
           val lengths = List.map List.length subgoals
           val derivations = ListUtil.multisplit lengths Ds
         in
           supervalidation (ListPair.map (fn (v, d) => v d) (validations, derivations))
         end)
  in
    fun THENL_LAZY (tac1, tacn) g =
      case tac1 g of
           ([], validation1) => ([], validation1)
         | (subgoals1, validation1) =>
             let
               val (subgoals2, validations2) =
                 ListPair.unzip (ListPair.mapEq (fn (f,x) => f x) (tacn (), subgoals1))
             in
               refine (validation1, subgoals2, validations2)
             end

    fun THEN_LAZY (tac1, tac2) g =
      case tac1 g of
           ([], validation1) => ([], validation1)
         | (subgoals1, validation1) =>
             let
               val (subgoals2, validations2) = ListPair.unzip (List.map (tac2 ()) subgoals1)
             in
               refine (validation1, subgoals2, validations2)
             end
  end

  fun THENL (tac1, tacn) =
    THENL_LAZY (tac1, fn () => tacn)

  fun THEN (tac1, tac2) =
    THEN_LAZY (tac1, fn () => tac2)

  fun ORELSE_LAZY (tac1, tac2) g =
    tac1 g handle _ => tac2 () g

  fun ORELSE (tac1, tac2) =
    ORELSE_LAZY (tac1, fn () => tac2)

  fun REPEAT tac =
    THEN_LAZY (tac, fn () => REPEAT tac)

  fun TRY tac =
    ORELSE(tac, ID)
end

