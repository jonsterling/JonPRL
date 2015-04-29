structure Variable :> VARIABLE =
struct

  type t = string * int
  type ord_key = t

  val counter = ref 0

  fun new () =
    let
      val (ref n) = counter
    in
      (counter := n + 1 ; ("", n))
    end

  fun named s =
    let
      val (ref n) = counter
    in
      (counter := n + 1 ; (s, n))
    end

  fun eq (_, n : int) (_, m) = (n = m)

  fun compare ((_, n), (_, m)) = Int.compare (n, m)

  fun to_string (s, x) =
    (case s of
         "" => "@"
      |  _ => s)
    ^ (Int.toString x)
end

