functor Library (R : REFINER_TYPES) :
  LIBRARY
    where type tactic = R.tactic
    and type goal = R.goal
    and type evidence = R.evidence =
struct
  structure V = Variable ()
  structure C = Context (V)

  type t = V.t
  type goal = R.goal
  type evidence = R.evidence
  type tactic = R.tactic

  val installed_lemmas : (goal * (evidence Susp.susp)) C.context ref = ref (C.empty)

  fun save name goal tac =
    let
      val (subgoals, validation) = tac goal
      val evidence =
        if null subgoals
        then Susp.delay (fn () => validation [])
        else
          let
            val readout = List.foldl (fn (g,r) => r ^ "\n" ^ R.print_goal g) "" subgoals
          in
            raise Fail ("Remaining subgoals: " ^ readout)
          end
      val key = V.named name
    in
      installed_lemmas := C.insert (! installed_lemmas) key (goal, evidence);
      key
    end

  fun all () =
    C.foldri (fn (k, _, memo) => k :: memo) [] (! installed_lemmas)

  fun name k =
    V.to_string PrintMode.User k

  fun lookup_lemma k =
    let
      val library = ! installed_lemmas
      val (SOME lemma) = C.lookup library k
    in
      lemma
    end

  fun goal lem =
    let
      val (P, E) = lookup_lemma lem
    in
      P
    end

  fun validate lemma =
    Susp.force (#2 (lookup_lemma lemma))

end
