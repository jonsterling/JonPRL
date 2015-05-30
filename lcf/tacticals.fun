functor Tacticals (Lcf : LCF) : TACTICALS =
struct
  open Lcf

  fun ID g =
    ([g], fn [D] => D | _ => raise Fail "ID")

  fun map_shape [] _ _ =  []
    | map_shape (n1::nums) (f1::funcs) args =
        let
          val (f1_args,args') = ListUtil.split_at n1 args
        in
          f1 f1_args :: map_shape nums funcs args'
        end
    | map_shape _ _ _ = raise Subscript

  local
    fun refine (supervalidation, subgoals, validations) =
      (List.concat subgoals,
       supervalidation o
         map_shape (map length subgoals) validations)
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

  fun TRY tac =
    ORELSE(tac, ID)

  fun REPEAT tac = TRY (THEN_LAZY (tac, fn () => TRY (REPEAT tac)))
end
