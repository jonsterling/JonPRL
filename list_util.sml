structure ListUtil :
sig
  val split : int -> 'a list -> 'a list * 'a list
  val multisplit : int list -> 'a list -> 'a list list
end =
struct
  local
    fun go _ [] = ([], [])
      | go 1 (x::xs) = ([x], xs)
      | go m (x::xs) =
        let val
          (xs', xs'') = go (m - 1) xs
        in
          (x::xs', xs'')
        end
  in
    fun split n ls =
      if n < 0
      then raise Subscript
      else if n = 0
      then ([], ls)
      else go n ls
  end

  fun multisplit [] xs = [xs]
    | multisplit (n::ns) xs =
      let
        val (ys,rem) = split n xs
      in
        ys :: multisplit ns rem
      end
end

