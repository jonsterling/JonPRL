structure Main =
struct
  fun main (_, files) =
    let
      fun load_file (f, dev) = CttFrontend.load_file (dev, f)

      val D =
        SOME (foldl load_file Development.empty files)
        handle e => (print (exnMessage e); NONE)
    in
      case D of
           NONE => 1
         | SOME development =>
              (CttFrontend.print_development development; 0)
              handle e => (print ("Error: " ^ exnMessage e ^ "\n");1)
    end
end
