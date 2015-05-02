structure Test =
struct
  val print_mode = PrintMode.User

  structure Var = Variable ()
  structure Syn =
    AbtUtil (Abt (structure Operator = Lang and Variable = Var))

  structure Refiner =
    Refiner
      (structure Syn = Syn
       val print_mode = print_mode)

  open Lang Syn Refiner
  open CoreTactics DerivedTactics InferenceRules
  infix $$ \\ THEN THENL ORELSE

  exception RemainingSubgoals of goal list

  fun check P (tac : tactic) =
  let
    val (subgoals, validate) = tac (Context.empty, P)
    val result =
      if null subgoals
      then validate []
      else
        let
          val readout = List.foldl (fn (g,r) => r ^ "\n" ^ print_goal g) "" subgoals
        in
          raise Fail ("Remaining subgoals: " ^ readout)
        end
  in
    (print ("Theorem: " ^ Syn.to_string print_mode P ^ "\n");
     print ("Evidence: " ^ Evidence.to_string print_mode result ^ "\n");
     print ("Extract: " ^ Syn.to_string print_mode (extract result) ^ "\n\n"))
  end

  val void = VOID $$ #[]
  val unit = UNIT $$ #[]
  val ax = AX $$ #[]

  fun & (a, b) = PROD $$ #[a, Variable.new() \\ b]
  infix &

  fun pair m n = PAIR $$ #[m,n]
  fun fst m = FST $$ #[m]
  fun lam e =
    let
      val x = Var.new ()
    in
      LAM $$ #[x \\ e x]
    end

  fun ~> (a, b) = FUN $$ #[a,Variable.new () \\ b]
  infixr ~>

  fun mem (m, a) = MEM $$ #[m,a]
  infix mem

  val _ =
      check
        (unit & (unit & unit))
        (ProdIntro ax THENL [Auto, ProdIntro ax THEN Auto])

  val _ =
     check
       (unit ~> (unit & unit))
       (FunIntro THENL [ProdIntro ax THEN Auto, Auto])

  val _ =
      check
        (fst (pair ax ax) mem unit)
        Auto

  val _ =
      check
        (lam (fn x => `` x) mem (unit ~> unit))
        Auto

  val _ =
      check
        (lam (fn x => pair ax ax) mem (void ~> void))
        (MemIntro THEN EqIntro THEN LamEq THENL [VoidElim THEN Auto, Auto])

  val _ =
      check
        (void ~> (unit & unit))
        (FunIntro THENL [VoidElim THEN Auto, Auto])

  val _ =
      check
        (unit ~> (unit & unit))
        (Witness (lam (fn x => pair (`` x) (`` x))) THEN Auto)
end

