structure Main =
struct
  datatype mode =
      CHECK_DEVELOPMENT
    | PRINT_DEVELOPMENT
    | LIST_OPERATORS
    | LIST_TACTICS
    | HELP
    | LOAD_CONFIG of mode

  local
    fun go [] = PRINT_DEVELOPMENT
      | go ("--check" :: _) = CHECK_DEVELOPMENT
      | go ("--list-operators" :: _) = LIST_OPERATORS
      | go ("--list-tactics" :: _) = LIST_TACTICS
      | go ("--help" :: _) = HELP
      | go ("--config" :: xs) = LOAD_CONFIG (go xs)
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

      fun loadFiles () = Frontend.loadFiles (Development.empty, files)
      fun loadConfigs () = Frontend.loadConfigs files
    in
      (case mode of
           CHECK_DEVELOPMENT => (loadFiles (); 0)
         | PRINT_DEVELOPMENT => (Frontend.printDevelopment (loadFiles ()); 0)
         | LIST_OPERATORS => (Frontend.printOperators (loadFiles ()); 0)
         | LIST_TACTICS => (Frontend.printTactics (loadFiles ()); 0)
         | HELP => (print helpMessage; 0)
         | LOAD_CONFIG CHECK_DEVELOPMENT => (loadConfigs (); 0)
         | LOAD_CONFIG PRINT_DEVELOPMENT =>
           (Frontend.printDevelopment (loadConfigs ()); 0)
         | LOAD_CONFIG LIST_OPERATORS =>
           (Frontend.printOperators (loadConfigs ()); 0)
         | LOAD_CONFIG LIST_TACTICS =>
           (Frontend.printTactics (loadConfigs ()); 0)
         | _ => 1)
      handle E => (print (exnMessage E); 1)
    end
end
