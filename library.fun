functor Library (R : REFINER_TYPES) : LIBRARY =
struct
  structure V = Variable ()
  structure C = Context (V)

  type t = V.t
  open R

  type object = {goal: goal, evidence: evidence Susp.susp}
  val library : object C.context ref = ref C.empty

  fun save name goal tac =
    let
      val (subgoals, validation) = tac goal
      val evidence =
        if null subgoals
        then Susp.delay (fn () => validation [])
        else
          let
            val readout = List.foldl (fn (g,r) => r ^ "\n" ^ R.goal_to_string PrintMode.Debug g) "" subgoals
          in
            raise Fail ("Remaining subgoals: " ^ readout ^ "\n")
          end
      val key = V.named name
    in
      library := C.insert (! library) key Visibility.Visible {goal = goal, evidence = evidence};
      key
    end

  fun all () =
    List.foldr (fn ((k, _, _), memo) => k :: memo) []
    (C.list_items (!  library))

  val name = V.to_string PrintMode.User
  fun lookup k = C.lookup (! library) k
  val goal = #goal o lookup
  val validate = Susp.force o #evidence o lookup
end
