structure Main =
struct
  fun main (_, args) =
    let
      val (opts, files) = List.partition (String.isPrefix "--") args
      val check_mode = List.exists (fn opt => opt = "--check") opts

      fun load_file (f, dev) = CttFrontend.load_file (dev, f)

      val D =
        SOME (foldl load_file Development.empty files)
        handle e => (print (exnMessage e); NONE)
    in
      case D of
           NONE => 1
         | SOME development =>
             if check_mode then
               0
             else
              (CttFrontend.print_development development; 0)
              handle e => (print ("Error: " ^ exnMessage e ^ "\n"); 1)
    end
end
