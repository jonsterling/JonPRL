structure Level :> LEVEL =
struct
  type t = int

  type constraint = int
  type substitution = int -> int

  exception LevelError

  fun max (i, j) = Int.max (i, j)

  fun succ i = i + 1
  fun pred i = if i > 0 then i - 1 else raise LevelError
  val base = 0

  local
    fun ticks 0 R = R
      | ticks n R = ticks (n - 1) (#"'" :: R)
  in
    fun toString i =
      "i" ^ String.implode (ticks i [])
  end

  fun assertLt (i, j) = if i < j then () else raise LevelError
  fun assertEq (i, j) = if i = j then () else raise LevelError

  fun yank x = fn y => x + y
  fun pred x = x - 1
  fun unify (x, y) = y - x

  local
    fun go [] = 0
      | go (x :: xs) =
          if List.all (fn y => x = y) xs then
            x
          else
            raise LevelError
  in
    fun resolve xs = fn x => x + go xs
  end

  fun subst f x = f x

  local
    open ParserCombinators CharParser
    infix wth >>
  in
    val parse : t charParser = char #"i" >> repeat (char #"'") wth length
  end
end
