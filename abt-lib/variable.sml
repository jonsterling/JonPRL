structure Variable :> VARIABLE =
struct

  type t = string option * int
  type ord_key = t

  val counter = ref 0

  fun new () =
    let
      val (ref n) = counter
    in
      (counter := n + 1 ; (NONE, n))
    end

  fun named s =
    let
      val (ref n) = counter
    in
      (counter := n + 1 ; (SOME s, n))
    end

  fun eq (_, n : int) (_, m) = (n = m)

  fun compare ((_, n), (_, m)) = Int.compare (n, m)

  fun name (s, x) = s

  fun to_string mode (s, x) =
    case mode of
         PrintMode.User =>
           (case s of
                 NONE => "@" ^ Int.toString x
               | SOME s' => s')
       | PrintMode.Debug =>
           (case s of
                 NONE => "@"
               | SOME s' => s')
            ^ Int.toString x
end

