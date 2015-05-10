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

  val void = VOID $$ #[]
  val unit = UNIT $$ #[]
  val ax = AX $$ #[]

  fun & (a, b) = PROD $$ #[a, Variable.named "x" \\ b]
  infix &

  fun pair m n = PAIR $$ #[m,n]
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

  val test1 =
    install_lemma "test1" (unit & (unit & unit))
      (ProdIntro ax THEN (TRY (ProdIntro ax)) THEN Auto)

  val test1' =
    install_lemma "test1'" (unit & (unit & unit))
      (Lemma test1)

  val z = Variable.named "z"

  val test2 =
    install_lemma "test2" (unit ~> (unit & unit))
      (FunIntro z THENL [ProdIntro ax THEN Auto, Auto])

  val test3 =
    install_lemma "test3" (lam (fn x => `` x) mem (unit ~> unit))
      Auto

  val test4 =
    install_lemma "test4" (lam (fn x => pair ax ax) mem (void ~> void))
      (MemUnfold THEN ReduceGoal THEN LamEq z THENL [VoidElim THEN Auto, Auto])

  val test5 =
    install_lemma "test5" (void ~> (unit & unit))
      (FunIntro z THENL [VoidElim THEN Auto, Auto])

  val test6 =
    install_lemma "test6" (unit ~> (unit & unit))
      (Witness (lam (fn x => pair (`` x) (`` x))) THEN Auto)

 local
   val x = Variable.named "x"
   val y = Variable.named "y"
  in
    val test7 =
      install_lemma "test7" ((void & unit) ~> void)
        (FunIntro z THENL
          [ ProdElim z (x, y) THEN Assumption
          , Auto
          ])
  end

  fun print_lemma lemma =
    let
      val P = lemma_goal lemma
      val evidence = validate_lemma lemma
    in
      print ("\n" ^ lemma_name lemma ^ "\n");
      print "----------------------------------------\n";
      print ("Goal: " ^ Syn.to_string print_mode P ^ "\n");
      print ("Evidence: " ^ Evidence.to_string print_mode evidence ^ "\n");
      print ("Extract: " ^ Syn.to_string print_mode (extract evidence) ^ "\n\n")
    end

  val _ =
    List.map print_lemma (all_lemmas ())
end

