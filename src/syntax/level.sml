structure Level :> LEVEL =
struct
  type t = int

  local
    fun ticks 0 R = R
      | ticks n R = ticks (n - 1) (#"'" :: R)
  in
    fun toString i =
      "i" ^ String.implode (ticks i [])
  end

  exception LevelError
  fun assertLt (i, j) = if i < j then () else raise LevelError
  fun unify (i, j) = if i = j then i else raise LevelError
  fun max (i, j) = Int.max (i, j)

  fun succ i = i + 1
  fun pred i = if i > 0 then i - 1 else raise LevelError
  val base = 0

  local
    open ParserCombinators CharParser
    infix wth >>
  in
    val parse : t charParser = char #"i" >> repeat (char #"'") wth length
  end
end
