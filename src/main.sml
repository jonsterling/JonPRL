structure Main =
struct
  datatype mode =
      CHECK_DEVELOPMENT
    | PRINT_DEVELOPMENT
    | LIST_OPERATORS
    | LIST_TACTICS

  val listOfTactics =
    ["intro [TERM]? #NUM? <NAME*>?",
     "elim #NUM [TERM]? <NAME*>?",
     "eq-cd [TERM*]? <NAME*>? @LEVEL?",
     "ext <NAME>? @LEVEL?",
     "symmetry",
     "capprox",
     "creflexivty",
     "areflexivty",
     "csymmetry",
     "step",
     "cstruct",
     "assumption",
     "assert [TERM] <NAME>?",
     "mem-cd",
     "auto NUM?",
     "reduce NUM?",
     "lemma <NAME>",
     "cut-lemma <NAME>",
     "unfold <(NAME @NUM)+>",
     "refine <NAME>",
     "witness [TERM]",
     "hypothesis #NUM",
     "bot-div #NUM",
     "hyp-subst (←|→) #NUM [TERM] @NUM?",
     "id",
     "fail",
     "trace \"MESSAGE\"",
     "cum @NUM?",
     "focus NUM #{TACTIC}"]

  local
    fun go [] = PRINT_DEVELOPMENT
      | go ("--check" :: _) = CHECK_DEVELOPMENT
      | go ("--list-operators" :: _) = LIST_OPERATORS
      | go ("--list-tactics" :: _) = LIST_TACTICS
      | go (_ :: xs) = go xs
  in
    fun getMode args = go args
  end

  fun main (_, args) =
    let
      val (opts, files) = List.partition (String.isPrefix "--") args
      val mode = getMode opts

      fun loadFile (f, dev) = CttFrontend.loadFile (dev, f)
      val oworld = SOME (foldl loadFile Development.empty files) handle _ => NONE
    in
      case oworld of
           NONE => 1
         | SOME world =>
             (case mode of
                   CHECK_DEVELOPMENT => 0
                 | PRINT_DEVELOPMENT =>
                   (CttFrontend.printDevelopment world; 0)
                 | LIST_OPERATORS =>
                   (CttFrontend.printOperators world; 0)
                 | LIST_TACTICS =>
                     (app (fn tac => print (tac ^ "\n")) listOfTactics; 0))
    end
end
