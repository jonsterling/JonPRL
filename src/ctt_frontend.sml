structure CttFrontend =
struct
  structure Extract = Extract(Syntax)

  val printDevelopment =
    let
      open Development.Telescope.ConsView
      fun go Empty = ()
        | go (Cons (lbl, obj, tele)) =
            (print (Development.Object.toString (lbl, obj) ^ "\n\n");
             go (out tele))
    in
      go o out o Development.enumerate
    end

  val printOperators =
    let
      open Development.Telescope.ConsView Development.Object
      fun printStep (lbl, arity) =
        print (Development.Telescope.Label.toString lbl ^ " " ^ Arity.toString arity ^ "\n")

      fun go Empty = ()
        | go (Cons (lbl, OPERATOR {arity,...}, rest)) =
          (printStep (lbl, arity); go (out rest))
        | go (Cons (lbl, THEOREM {...}, rest)) =
          (printStep (lbl, #[]); go (out rest))
        | go (Cons (_, _, rest)) =
          go (out rest)
    in
      go o out o Development.enumerate
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

      open CttDevelopmentParser
    in
      (case CharParser.parseChars (parse initialContext) coordStream of
           Sum.INL e => raise Fail e
         | Sum.INR (bindings, ast) =>
           DevelopmentAstEval.eval initialDevelopment ast)
      handle E => (print ("\n\n" ^ prettyException E ^ "\n"); raise E)
    end
end
