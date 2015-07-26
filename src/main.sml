structure Main =
struct
  datatype mode =
      CHECK_DEVELOPMENT
    | PRINT_DEVELOPMENT
    | LIST_OPERATORS
    | LIST_TACTICS
    | HELP

  local
    fun go [] = PRINT_DEVELOPMENT
      | go ("--check" :: _) = CHECK_DEVELOPMENT
      | go ("--list-operators" :: _) = LIST_OPERATORS
      | go ("--list-tactics" :: _) = LIST_TACTICS
      | go ("--help" :: _) = HELP
      | go (_ :: xs) = go xs
  in
    fun getMode args = go args
  end

  val helpMessage =
    "A proof assistant based on Computational Type Theory\n" ^
    "Usage\n" ^
    "  jonprl <file>...\n" ^
    "  jonprl --check <file>...\n" ^
    "  jonprl --help\n" ^
    "  jonprl --list-operators <file>...\n" ^
    "  jonprl --list-tactics <file>...\n" ^
    "Options\n" ^
    "  --help            Print this message\n" ^
    "  --check           Check a development without printing validations/extracts\n" ^
    "  --list-operators  After checking development list out all available operators\n" ^
    "  --list-tactics    After checking development list out all available tactics\n"


  fun main (_, args) =
    let
      val (opts, files) = List.partition (String.isPrefix "--") args
      val mode = getMode opts

      (* Print help message and exit early *)
      val () =
          case mode of
              HELP => (print helpMessage; OS.Process.exit OS.Process.success)
            | _ => ()

      fun loadFile (f, dev) = Frontend.loadFile (dev, f)
      val oworld =
        SOME (foldl loadFile Development.empty files)
          handle E =>
            (print (exnMessage E); NONE)
    in
      case oworld of
           NONE => 1
         | SOME world =>
             (case mode of
                   CHECK_DEVELOPMENT => 0
                 | PRINT_DEVELOPMENT =>
                   ((Frontend.printDevelopment world; 0)
                     handle E => (print (exnMessage E); 1))
                 | LIST_OPERATORS =>
                   ((Frontend.printOperators world; 0)
                     handle E => (print (exnMessage E); 1))
                 | LIST_TACTICS =>
                   ((Frontend.printTactics world; 0)
                     handle E => (print (exnMessage E); 1))
                 | HELP => 0)
    end
end
