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

  fun subst e v e' =
    case out e' of
      ` v' => if Variable.eq v v' then e else e'
    | v' \ e'' => if Variable.eq v v' then e' else (v' \\ subst e v e'')
    | p $ es => p $$ Vector.map (subst e v) es

  fun to_string mode e =
    case out e of
      ` v => Variable.to_string mode v
    | v \ e => Variable.to_string mode v ^ "." ^ (to_string mode e)
    | p $ es =>
        Operator.to_string p ^
          (if Vector.length es = 0 then ""
             else VectorUtil.to_string (to_string mode) es)

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
