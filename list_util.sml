structure ListUtil :
sig
  val split : int -> 'a list -> 'a list * 'a list
  val multisplit : int list -> 'a list -> 'a list list
end =
struct
  exception Hole

  local
    fun go 0 (xs, ys) = (xs, ys)
      | go n (xs, []) = ([], xs)
      | go n (xs, y::ys) = go (n - 1) (xs @ [y], ys)
  in
    fun split i xs = go i ([], xs)
  end

  local
    fun go [] xs r = r @ [xs]
      | go (n::ns) xs r =
        let
          val (ys,zs) = split n xs
        in
          go ns zs (r @ [ys])
        end
  in
    fun multisplit ns xs = go ns xs []
  end
end

