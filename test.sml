structure Test =
struct
  val print_mode = PrintMode.Debug

  structure Var = StringVariable
  structure Syn =
    AbtUtil (Abt (structure Operator = Operator and Variable = Var))

 structure Sequent =
   Sequent
     (structure Context = Context(Syn.Variable)
      structure Syntax = Syn)

  structure Refiner =
    Refiner
      (structure Syn = Syn
       structure Sequent = Sequent
       val print_mode = print_mode)

  structure Extract = Extract(Syn)

  open Operator Syn Refiner
  open CoreTactics DerivedTactics InferenceRules Sequent

  infix 2 >>
  infix 7 $$
  infix \\ THEN THENL ORELSE

  fun univ i = UNIV i $$ #[]
  val void = VOID $$ #[]
  val unit = UNIT $$ #[]
  val ax = AX $$ #[]
  fun squash A = SQUASH $$ #[A]

  fun & (a, b) = PROD $$ #[a, Variable.named "x" \\ b]
  infix 6 &

  val % = Variable.named

  fun pair m n = PAIR $$ #[m,n]
  fun lam e =
    let
      val x = %"x"
    in
      LAM $$ #[x \\ e x]
    end

  fun pi a b =
    let
      val x = Var.named "x"
    in
      FUN $$ #[a, x \\ b x]
    end

  fun sg a b =
    let
      val x = Var.named "x"
    in
      PROD $$ #[a, x \\ b x]
    end

  fun ap (m, n) =
    AP $$ #[m, n]
  infix 1 ap

  fun ~> (a, b) = FUN $$ #[a,Variable.named "x" \\ b]
  infixr 5 ~>

  fun mem (m, a) = MEM $$ #[m,a]
  infix 5 mem

  val Emp = Context.empty

  val test1 =
    Library.save "test1" (Emp >> unit & (unit & unit))
      (ProdIntro ax THEN (TRY (ProdIntro ax)) THEN Auto)

  val test1' =
    Library.save "test1'" (Emp >> unit & (unit & unit))
      (Lemma test1)

  val test2 =
    Library.save "test2" (Emp >> unit ~> (unit & unit))
      (FunIntro NONE NONE THEN Auto THEN ProdIntro ax THEN Auto)

  val test3 =
    Library.save "test3" (Emp >> lam (fn x => `` x) mem (unit ~> unit))
      Auto

  val test4 =
    Library.save "test4" (Emp >> lam (fn x => pair ax ax) mem (void ~> void))
      (MemUnfold THEN LamEq NONE NONE THEN Auto THEN VoidElim THEN Auto)

  val test5 =
    Library.save "test5" (Emp >> void ~> (unit & unit))
      (FunIntro NONE NONE THEN Auto THEN VoidElim THEN Auto)

  val test6 =
    Library.save "test6" (Emp >> unit ~> (unit & unit))
      (Witness (lam (fn x => pair (`` x) (`` x))) THEN Auto
       THEN PairEq NONE NONE)

  val test7 =
    Library.save "test7" (Emp >> (void & unit) ~> void)
      (FunIntro (SOME "z") NONE THEN Auto THEN ProdElim "z" ("x", "y") THEN Auto)

  val test8 =
    Library.save "test8" (Emp >> (univ 0) mem (univ 2))
      Auto

  val test9 =
    Library.save "test9" (Emp >> (univ 0 & unit) mem (univ 1))
      Auto

  val squash_test =
    Library.save "squash_test" (Emp >> squash (unit & unit))
      (Auto THEN ProdIntro ax THEN Auto)

  local
    val ac_premise =
      FUN $$ #[ ``"A", "a" \\
        PROD $$ #[ ``"B", "b" \\
          ``"Q" ap ``"a" ap ``"b"]]

    val ac_conclusion =
      PROD $$ #[ ``"A" ~> ``"B", "f" \\
        FUN $$ #[ ``"A", "a" \\
          ``"Q" ap ``"a" ap (``"f" ap ``"a")]]

    val ac_prop =
      FUN $$ #[univ 0, "A" \\
        FUN $$ #[univ 0, "B" \\
          FUN $$ #[ (``"A" ~> (``"B" ~> univ 0)), "Q" \\
            ac_premise ~> ac_conclusion ]]]

  fun fst M =
    SPREAD $$ #[M, "u" \\ ("v" \\ ``"u")]

  in
    val _ =
      Library.save "ac" (Emp >> ac_prop)
      (Auto
       THEN ProdIntro (LAM $$ #["z" \\ fst (``"x" ap ``"z")])
       THEN Auto
       THEN Admit
       )
  end

  fun print_lemma lemma =
    let
      val gl = Library.goal lemma
      val evidence = Library.validate lemma
    in
      print ("\n" ^ Library.name lemma ^ "\n");
      print "----------------------------------------\n";
      print ("Goal: " ^ Sequent.to_string print_mode gl ^ "\n");
      print ("Evidence: " ^ Syn.to_string print_mode evidence ^ "\n");
      print ("Extract: " ^ Syn.to_string print_mode (Extract.extract evidence) ^ "\n\n")
    end

  val _ =
    List.map print_lemma (Library.all ())
end
