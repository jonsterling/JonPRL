structure Test =
struct
  structure Extract = Extract(Syntax)
  structure Var = Syntax.Variable
  structure Tacticals = Tacticals(Lcf)

  open Operator Syntax Tacticals Conversionals CttUtil Sequent
  open Rules Conversions

  infix 2 >>
  infix 7 $$
  infix \\ THEN THENL ORELSE

  val % = Sum.outR o CharParser.parseString Syntax.parse_abt
  val %% = Sum.outR o CharParser.parseString CttScript.parse
  val %! = Sum.outL o CharParser.parseString CttScript.parse
  val Emp = Context.empty

  val test1 =
    Library.save "test1" (Emp >> %"Σ(unit; _. Σ(unit; _. unit))")
      (%%"prod-intro ⌊<>⌋; ?{prod-intro ⌊<>⌋}; auto.")

  val test1' =
    Library.save "test1'" (Emp >> %"Σ(unit; _. Σ(unit; _. unit))")
      (Lemma test1)

  val test2 =
    Library.save "test2" (Emp >> %"Π(unit; _. Σ(unit; _. unit))")
      (%%"fun-intro; auto; prod-intro ⌊<>⌋; auto.")

  val test3 =
    Library.save "test3" (Emp >> %"∈(λ(x. x); Π(unit; _. unit))")
      (%%"auto.")

  val test4 =
    Library.save "test4" (Emp >> %"∈(λ(x.pair(x;x)); Π(void;_.void))")
      (%%"auto; void-elim; auto.")

  val test5 =
    Library.save "test5" (Emp >> %"Π(void; _. Σ(unit; _.unit))")
      (%%"fun-intro; auto; void-elim; auto.")

  val test6 =
    Library.save "test6" (Emp >> %"Π(unit; _. Σ(unit; _.unit))")
      (%%"witness ⌊λ(x. pair(x;x))⌋; auto.")

  val test7 =
    Library.save "test7" (Emp >> %"Π(Σ(void;_.unit); _. void)")
      (%%"fun-intro <z>; auto; prod-elim <z>; auto.")

  val test8 =
    Library.save "test8" (Emp >> %"∈(U<0>; U<2>)")
      (%%"auto.")

  val test9 =
    Library.save "test9" (Emp >> %"∈(Σ(U<0>; _.unit); U<1>)")
      (%%"auto.")

  val squash_test =
    Library.save "squash_test" (Emp >> %"!(Σ(unit;_.unit))")
      (%%"auto; prod-intro ⌊<>⌋; auto.")

  local
    val ac_prop =
      %"∀(U<0>; A. ∀(U<0>; B. ∀(Π(A; _. Π(B; _. U<0>)); Q. Π(Π(A; a. Σ(B; b. ap(ap(Q;a);b))); φ. Σ(Π(A; _.B); f. Π(A; a. ap(ap(Q;a);ap(f;a))))))))"
  in
    val _ =
      Library.save "ac" (Emp >> ac_prop)
        (%%"auto; prod-intro ⌊λ(w. spread(ap(φ;w); x.y.x))⌋; auto; \
          \ fun-elim <φ> ⌊a⌋; auto; \
          \ subst ⌊=(ap(φ;a); y; Σ(B;b. ap(ap(Q;a);b)))⌋ ⌊z. ap(ap(Q;a); spread(z; x.y.x))⌋; \
          \ ?{ symmetry }; auto; \
          \ prod-elim <y>; auto.")
  end

  fun print_lemma lemma =
    let
      val gl = Library.goal lemma
      val evidence = Library.validate lemma
    in
      print ("\n" ^ Library.name lemma ^ "\n");
      print "----------------------------------------\n";
      print ("Goal: " ^ Sequent.to_string gl ^ "\n");
      print ("Evidence: " ^ Syntax.to_string evidence ^ "\n");
      print ("Extract: " ^ Syntax.to_string (Extract.extract evidence) ^ "\n\n")
    end

  val _ =
    List.map print_lemma (Library.all ())
end
