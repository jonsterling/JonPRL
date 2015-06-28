structure CttFrontend =
struct
  structure Extract = Extract(Syntax)

  fun printDevelopment world =
    let
      open Development.Telescope
      fun go ConsView.Empty = ()
        | go (ConsView.Cons (lbl, obj, tele)) =
            (print (Development.Object.toString (lbl, obj) ^ "\n\n");
             go (ConsView.out tele))
    in
      go (ConsView.out (Development.enumerate world))
    end

  fun prettyException E =
    case E of
         AnnotatedLcf.RefinementFailed (exn as {error, goal, metadata as {name, pos}}) =>
           "[" ^ Pos.toString pos
           ^ "]: tactic '"
           ^ name
           ^ "' failed with goal: \n"
           ^ Sequent.toString goal
           ^ "\n\n" ^ prettyException error
       | TacticEval.RemainingSubgoals goals =>
           ("Remaining subgoals:" ^ foldl (fn (g,r) => r ^ "\n" ^ Sequent.toString g ^ "\n") "" goals)
       | Syntax.Malformed msg => "Syntax error: " ^ msg
       | _ => exnMessage E

  fun loadFile (initialDevelopment, name) : Development.world =
    let
      val instream = TextIO.openIn name
      val charStream = Stream.fromProcess (fn () => TextIO.input1 instream)
      fun is_eol s =
        case Stream.front s of
             Stream.Nil => true
           | Stream.Cons (x, s') => x = #"\n"
      val coordStream = CoordinatedStream.coordinate is_eol (Coord.init name) charStream
      val initialContext =
        StringVariableContext.new
          (Development.enumerateOperators initialDevelopment)
      fun updateDevelopment bindings =
        List.foldl
          (fn (bind, wld) => Development.declareOperator wld bind)
          initialDevelopment
          (StringVariableContext.enumerateOperators bindings)

      open CttDevelopmentParser
    in
      (case CharParser.parseChars (parse initialContext) coordStream of
           Sum.INL e => raise Fail e
         | Sum.INR (bindings, ast) =>
           DevelopmentAstEval.eval (updateDevelopment bindings) ast)
      handle E => (print ("\n\n" ^ prettyException E ^ "\n"); raise E)
    end
end
