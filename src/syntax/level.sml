structure Level :> LEVEL =
struct
  exception LevelError

  (* This structure gives an abstract type which may be converted
   * to and from integers >= 0.
   *)
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

  (* Constraints are represented as the difference between two
   * levels. So a constraint of 5 means we tried to unify level i
   * with level i'''''
   *)
  type constraint = int

  (* A substitution here is represented as a map across integers.
   * The idea being that all a substitution can do is move a level
   * up a certain number of levels or down a certain number of levels.
   * So in practice all substitutions are functions adding or
   * subtracting a constant amount.
   *)
  type substitution = int -> int

  (* All operations on universes are defined on the underling integer
   * representation.
   *)

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
