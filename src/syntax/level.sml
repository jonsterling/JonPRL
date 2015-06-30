structure Level :> LEVEL =
struct
  exception LevelError

  structure T :>
  sig
    eqtype t
    val into : int -> t
    val out : t -> int
  end =
  struct
    type t = int

    fun into i =
      if i >= 0 then
        i
      else
        raise LevelError

    fun out i = i
  end

  type t = T.t

  type constraint = int
  type substitution = int -> int

  fun max (i, j) = T.into (Int.max (T.out i, T.out j))

  fun succ i = T.into (T.out i + 1)
  fun pred i = T.into (T.out i - 1)
  val base = T.into 0

  local
    fun ticks 0 R = R
      | ticks n R = ticks (n - 1) (#"'" :: R)
  in
    fun toString i =
      "i" ^ String.implode (ticks (T.out i) [])
  end

  fun assertLt (i, j) = if T.out i < T.out j then () else raise LevelError
  fun assertEq (i, j) = if i = j then () else raise LevelError

  fun yank x = fn y => T.out x + y
  fun unify (x, y) = T.out y - T.out x

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

  fun subst f x =
    T.into (f (T.out x))

  local
    open ParserCombinators CharParser
    infix wth >>
  in
    val parse : t charParser = char #"i" >> repeat (char #"'") wth T.into o length
  end
end
