structure CttFrontend =
struct
  structure Extract = Extract(Syntax)

  fun load_file name =
    let
      exception RefinementFailed
      val instream = TextIO.openIn name
      val char_stream = Stream.fromProcess (fn () => TextIO.input1 instream)
      fun is_eol s =
        case Stream.front s of
             Stream.Nil => true
           | Stream.Cons (x, s') => x = #"\n"
      val coord_stream = CoordinatedStream.coordinate is_eol (Coord.init name) char_stream

      open CttDevelopmentParser
      open Development.Telescope

      val development =
        (case (CharParser.parseChars parse coord_stream) of
             Sum.INL e => raise Fail e
           | Sum.INR x => x)
        handle Development.RemainingSubgoals goals =>
          (print ("\n\nRemaining subgoals:" ^ foldl (fn (g,r) => r ^ "\n" ^ Lcf.goal_to_string g) "" goals ^ "\n\n");
          raise RefinementFailed)

      fun obj_to_string lbl (Development.Definition {definiens}) =
            lbl ^ " =def= ⌊" ^ Syntax.to_string definiens ^ "⌋."
        | obj_to_string lbl (Development.Theorem {statement, evidence,...}) =
            let
              val evidence' = Susp.force evidence
            in
              "Theorem " ^ lbl ^ " : ⌊" ^ Lcf.goal_to_string statement ^ "⌋ {\n  "
                ^ Syntax.to_string evidence' ^ "\n} ext {\n  "
                ^ Syntax.to_string (Extract.extract evidence') ^ "\n}."

            end
      fun go ConsView.Empty = ()
        | go (ConsView.Cons (lbl, obj, tele)) = (print (obj_to_string lbl obj ^ "\n\n"); go (ConsView.out tele))
    in
      go (ConsView.out (Development.out development))
    end
end
