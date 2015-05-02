functor CoreTactics (R : REFINER_TYPES) :
  CORE_TACTICS where type tactic = R.tactic =
struct
  type tactic = R.tactic

  fun ID g =
    ([g], fn [D] => D | _ => raise Fail "ID")

  fun THENL_LAZY (tac1, tacn) (g : R.goal) =
    case tac1 g of
         ([], validation1) => ([], validation1)
       | (subgoals1, validation1) =>
           let
             val (subgoals2, validations2) =
               ListPair.unzip (ListPair.map (fn (f,x) => f x) (tacn (), subgoals1))
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

  fun THEN_LAZY (tac1, tac2) (g : R.goal) =
    case tac1 g of
         ([], validation1) => ([], validation1)
       | (subgoals1, validation1) =>
           let
             val (subgoals2, validations2) = ListPair.unzip (List.map (tac2 ()) subgoals1)
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

  fun THENL (tac1, tacn) =
    THENL_LAZY (tac1, fn () => tacn)

  fun THEN (tac1, tac2) : tactic =
    THEN_LAZY (tac1, fn () => tac2)

  fun ORELSE (tac1, tac2) : tactic = fn g =>
    tac1 g handle _ => tac2 g

  fun ORELSE_LAZY (tac1, tac2) : tactic = fn g =>
    tac1 g handle _ => tac2 () g

  fun REPEAT tac = THEN_LAZY (tac, fn () => REPEAT tac)

  fun TRY tac = ORELSE(tac, ID)
end

