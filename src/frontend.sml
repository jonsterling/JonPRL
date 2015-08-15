structure Frontend =
struct
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

  local
    open Development.Telescope.ConsView Development.Object

    fun printStep theta =
      let
        val name = UniversalOperator.toString theta
        val arity = UniversalOperator.arity theta
      in
        print (name ^ " " ^ Arity.toString arity ^ "\n")
      end
  in
    fun printOperators world =
      (List.app
         (fn theta => printStep (CttCalculusInj.`> theta))
         CttCalculus.publicOperators;
       List.app
         (fn (_, theta, _) => printStep theta)
         (Development.enumerateOperators world))
  end

  fun printTactics world =
    List.app (fn x => print (x ^ "\n"))
             (Tactic.listOfTactics @ Development.enumerateTactics world)

  fun prettyException E =
    case E of
         AnnotatedLcf.RefinementFailed (exn as {error, goal, metadata as {name, pos}}) =>
           "[" ^ Pos.toString pos
           ^ "]: tactic '"
           ^ name
           ^ "' failed with goal: \n"
           ^ Goal.toString Sequent.toString goal
           ^ "\n\n" ^ prettyException error
       | TacticEval.RemainingSubgoals goals =>
           ("Remaining subgoals:\n" ^ foldl (fn (g,r) => r ^ "\n" ^ Goal.toString Sequent.toString g ^ "\n") "" goals)
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
        ParserContext.new
          (Development.enumerateOperators initialDevelopment)

      open CttDevelopmentParser
    in
      (case CharParser.parseChars (parse initialContext) coordStream of
           Sum.INL e => raise Fail e
         | Sum.INR (bindings, ast) =>
           DevelopmentAstEval.eval initialDevelopment ast)
      handle E => (print ("\n\n" ^ prettyException E ^ "\n"); raise E)
    end

  fun loadFiles (initialDevelopment, names) : Development.world =
    List.foldl ((fn (f, dev) => if OS.Path.ext f = SOME "cfg"
                                then loadConfig (dev, f)
                                else loadFile (dev, f)))
               initialDevelopment
               names
  and loadConfig (initialDevelopment, name) : Development.world =
    let
      val instream = TextIO.openIn name
      val charStream = Stream.fromProcess (fn () => TextIO.input1 instream)
      fun is_eol s =
        case Stream.front s of
             Stream.Nil => true
           | Stream.Cons (x, s') => x = #"\n"
      val coordStream = CoordinatedStream.coordinate is_eol (Coord.init name) charStream

      open OS.Path
      fun relativize file = joinDirFile {dir = dir name, file = file}
    in
      case CharParser.parseChars ConfigParser.parse coordStream of
          Sum.INL e => raise Fail e
        | Sum.INR names => loadFiles (initialDevelopment, List.map relativize names)
    end
end
