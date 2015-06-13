structure Main =
struct
  fun main (_, args) =
    let
      val (opts, files) = List.partition (String.isPrefix "--") args
      val checkMode = List.exists (fn opt => opt = "--check") opts

      fun loadFile (f, dev) = CttFrontend.loadFile (dev, f)

      val D =
        SOME (foldl loadFile Development.empty files)
        handle e => (print (exnMessage e); NONE)
    in
      case D of
           NONE => 1
         | SOME development =>
             if checkMode then
               0
             else
              (CttFrontend.printDevelopment development; 0)
              handle e => (print ("Error: " ^ exnMessage e ^ "\n"); 1)
    end
end
