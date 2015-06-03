structure Level :> LEVEL =
struct
  type t = int
  type constraint = int
  type substitution = int -> int
  exception LevelError

  fun yank x = fn y => x + y
  fun pred x = x - 1
  fun unify (x, y) = y - x

  local
    fun ticks 0 R = R
      | ticks n R = ticks (n - 1) (#"'" :: R)
  in
    fun to_string i =
      "i" ^ String.implode (ticks i [])
  end

  local
    open ParserCombinators CharParser
    infix wth >>
  in
    val parse : t charParser = char #"i" >> repeat (char #"'") wth length
  end

  local
    fun go [] = 0
      | go (x :: xs) =
          if (foldl (fn (y, b) => b andalso x = y) true xs) then
            x
          else
            raise LevelError
  in
    fun resolve xs = fn x => x + go xs
  end

  fun subst f x = f x

  val compare = Int.compare
  fun assert_lt (i, j) = if i < j then () else raise LevelError
  fun assert_lte (i, j) = if i <= j then () else raise LevelError
  fun assert_eq (i, j) = if i = j then i else raise LevelError
  fun max (i, j) = Int.max (i, j)
  fun prime i = i + 1
  val base = 0
end
