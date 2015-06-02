functor AbtUtil (A : ABT) : ABT_UTIL =
struct
  open A

  infix 5 $
  infix 5 $$
  infix 5 \
  infix 5 \\

  fun `` v = into (` v)
  fun v \\ e = into (v \ e)
  fun p $$ es = into (p $ es)

  local
    fun elem (X, x) = List.exists (fn y => Variable.eq (x, y)) X
  in
    local
      fun union ([], Y) = Y
        | union (x :: X, Y) = if elem (Y, x) then union (X, Y) else x :: (union (X,  Y))

      fun go X Y M =
        case out M of
             ` x => if elem (X, x) orelse elem (Y,x) then Y else (x :: Y)
           | x \ E => go (x :: X) Y E
           | p $ Es => Vector.foldl union Y (Vector.map (go X []) Es)
    in
      fun free_variables M = go [] [] M
    end

    local
      fun go X r (M, x) =
        case out M of
             ` y => if elem (X, y) then r else Variable.eq (x, y)
           | y \ E => go (y :: X) r (E, x)
           | p $ Es => Vector.foldl (fn (N,r') => r' orelse go X r' (N, x)) r Es
    in
      fun has_free (M, x) = go [] false (M, x)
    end
  end


  fun subst e v e' =
    case out e' of
      ` v' => if Variable.eq (v, v') then e else e'
    | v' \ e'' => if Variable.eq (v, v') then e' else (v' \\ subst e v e'')
    | p $ es => p $$ Vector.map (subst e v) es

  fun to_string_open F e =
    case out e of
      ` v => Variable.to_string v
    | v \ e =>
        let
          val v_str =
            if has_free (e, v)
            then Variable.to_string v
            else "_"
        in
          v_str ^ "." ^ F e
        end
    | p $ es =>
        Operator.to_string p ^
          (if Vector.length es = 0 then ""
             else VectorUtil.to_string F es)

  fun to_string e = to_string_open to_string e

  exception ExpectedBinding of t

  fun unbind e =
    case out e of
      v \ e => (v,e)
    | _ => raise ExpectedBinding e

  fun subst1 xe b =
    case unbind xe of
      (x,e) => subst b x e

  fun op // (x, y) = subst1 x y

end
