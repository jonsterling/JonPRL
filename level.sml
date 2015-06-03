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
    fun go [] R = R
      | go (0 :: xs) R = go xs R
      | go (x :: xs) 0 = go xs x
      | go (x :: xs) R =
          if (x > 0) andalso (R > 0) then
            go xs (Int.max (x, R))
          else if (x < 0) andalso (R < 0) then
            go xs (Int.min (x, R))
          else
            raise LevelError
  in
    fun resolve xs = fn x => x + go xs 0
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
