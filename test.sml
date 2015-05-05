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

  infix 4 >>
  infix 7 $$
  infix \\ THEN THENL ORELSE

  exception RemainingSubgoals of goal list

  fun check P (tac : tactic) =
  let
    val (subgoals, validate) = tac (Context.empty >> P)
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

  fun & (a, b) = PROD $$ #[a, Variable.named "x" \\ b]
  infix &

  fun pair m n = PAIR $$ #[m,n]
  fun fst m = FST $$ #[m]
  fun lam e =
    let
      val x = Var.named "x"
    in
      LAM $$ #[x \\ e x]
    end

  fun pi a b =
    let
      val x = Var.named "x"
    in
      FUN $$ #[a, x \\ b x]
    end

  fun ~> (a, b) = FUN $$ #[a,Variable.named "x" \\ b]
  infixr ~>

  fun mem (m, a) = MEM $$ #[m,a]
  infix mem

  val _ =
    check
      (unit & (unit & unit))
      (ProdIntro ax THEN (TRY (ProdIntro ax)) THEN Auto)

  val z = Variable.named "z"

  val _ =
    check
      (unit ~> (unit & unit))
      (FunIntro z THENL [ProdIntro ax THEN Auto, Auto])

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
        (MemIntro THEN EqIntro THEN LamEq z THENL [VoidElim THEN Auto, Auto])

  val _ =
      check
        (void ~> (unit & unit))
        (FunIntro z THENL [VoidElim THEN Auto, Auto])

  val _ =
      check
        (unit ~> (unit & unit))
        (Witness (lam (fn x => pair (`` x) (`` x))) THEN Auto)
end

