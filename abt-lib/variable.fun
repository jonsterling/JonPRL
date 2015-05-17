functor Variable () :> VARIABLE =
struct
  type t = string option * int

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

  fun compare ((SOME str, n), (SOME str', m)) =
    (case Int.compare (n, m) of
         EQUAL => String.compare (str, str')
       | order => order)
    | compare ((_, n), (_,m)) = Int.compare (n,m)

  fun eq (x : t) y = compare (x,y) = EQUAL

  fun clone (SOME s, _) = named s
    | clone _ = new ()

  val prime = clone

  local
    fun print_num i = Int.toString i
  in
    fun name (SOME s, x) = s
      | name (NONE, x) = "@" ^ print_num x

    fun to_string mode (s, x) =
      case mode of
           PrintMode.User =>
             (case s of
                   NONE => "@" ^ print_num x
                 | SOME s' => s')
         | PrintMode.Debug =>
             (case s of
                   NONE => "@"
                 | SOME s' => s')
              ^ print_num x
  end
end

structure StringVariable : VARIABLE =
struct
  type t = string
  fun named x = x
  fun eq (x : string) y = x = y
  val compare = String.compare
  fun name x = x
  fun to_string _ x = x
  fun clone x = x
  fun prime x = x ^ "'"
end
