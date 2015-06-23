structure Level :> LEVEL where type t = int =
struct
  type t = int

  fun toString i = Int.toString i

  exception LevelError
  fun assertLt (i, j) = if i < j then () else raise LevelError
  fun unify (i, j) = if i = j then i else raise LevelError
  fun max (i, j) = Int.max (i, j)
  fun pred i = if i <= 0 then raise LevelError else i - 1
  fun succ i = i + 1
end
