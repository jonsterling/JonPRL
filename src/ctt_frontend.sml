structure CttFrontend =
struct
  structure Extract = Extract(Syntax)

  fun print_development development =
    let
      open Development.Telescope
      fun go ConsView.Empty = ()
        | go (ConsView.Cons (lbl, obj, tele)) =
            (print (Development.Object.to_string (lbl, obj) ^ "\n\n");
             go (ConsView.out tele))
    in
      go (ConsView.out (Development.out development))
    end

  fun load_file (initial_development, name) : Development.t =
    let
      val instream = TextIO.openIn name
      val char_stream = Stream.fromProcess (fn () => TextIO.input1 instream)
      fun is_eol s =
        case Stream.front s of
             Stream.Nil => true
           | Stream.Cons (x, s') => x = #"\n"
      val coord_stream = CoordinatedStream.coordinate is_eol (Coord.init name) char_stream

      open CttDevelopmentParser
    in
      (case (CharParser.parseChars (parse initial_development) coord_stream) of
           Sum.INL e => raise Fail e
         | Sum.INR x => x)
      handle
          Development.RemainingSubgoals goals =>
            (print ("\n\nRemaining subgoals:" ^ foldl (fn (g,r) => r ^ "\n" ^ Lcf.goal_to_string g ^ "\n") "" goals ^ "\n\n");
            raise Development.RemainingSubgoals goals)
        | AnnotatedLcf.RefinementFailed (exn as {error, goal, metadata as {name,pos}}) =>
            (print
              ("\n\n[" ^ Pos.toString pos
                 ^ "]: tactic '" ^ name ^ "' failed (" ^ exnMessage error ^ ") with goal: \n" ^ Sequent.to_string goal ^ "\n\n");
            raise AnnotatedLcf.RefinementFailed exn)
    end
end
