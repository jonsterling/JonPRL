structure Level :> LEVEL where type t = int =
struct
  type t = int

  fun to_string i = Int.toString i

  exception LevelError
  val compare = Int.compare
  fun assert_lt (i, j) = if i < j then () else raise LevelError
  fun unify (i, j) = if i = j then i else raise LevelError
  fun max (i, j) = Int.max (i, j)
  fun prime i = i + 1
end
