functor Abt
  (structure Operator : OPERATOR
   structure Variable : VARIABLE) : ABT =
struct
  structure Operator = Operator
  structure Variable = Variable

  infix 5 \
  infix 5 $

  datatype t
    = FREE of Variable.t
    | BOUND of int
    | ABS of Variable.t * t
    | APP of Operator.t * t vector

  datatype 'a view
    = ` of Variable.t
    | \ of Variable.t * 'a
    | $ of Operator.t * 'a vector

  fun map f (` v) = ` v
    | map f (v \ e') = v \ f e'
    | map f (p $ es) = p $ Vector.map f es

  fun shiftvar v n (FREE v') = if Variable.eq (v, v') then BOUND n else (FREE v')
    | shiftvar v n (BOUND m) = BOUND m
    | shiftvar v n (ABS (x, e')) = ABS (x, shiftvar v (n + 1) e')
    | shiftvar v n (APP (p, es)) = APP (p, Vector.map (shiftvar v n) es)

  fun match_arity (0, ABS _) = false
    | match_arity (0, _) = true
    | match_arity (n, ABS (_, e')) = match_arity (n - 1, e')
    | match_arity (n, _) = false

  exception Malformed of string

  fun doapp (oper, es) =
    if VectorUtil.pair_all_eq match_arity (Operator.arity oper, es)
    then APP (oper, es)
    else raise Malformed ("Bad arity: " ^ Operator.to_string oper)

  fun into (` v) = FREE v
    | into (v \ e') = ABS (v, shiftvar v 0 e')
    | into (p $ es) = doapp (p, es)

  fun addvar v n (FREE v') = FREE v'
    | addvar v n (BOUND m) = if m = n then FREE v else BOUND m
    | addvar v n (ABS (x, e)) = ABS (x, addvar v (n + 1) e)
    | addvar v n (APP (p, es)) = APP (p, Vector.map (addvar v n) es)

  fun out e =
    case e of
      FREE v => ` v
    | BOUND n => raise Malformed "bound variable occured in out"
    | ABS (x, e') =>
      let
        val v = Variable.clone x
      in
        v \ addvar v 0 e'
      end
    | APP (p, es) => p $ es

  fun eq (FREE v1, FREE v2) = Variable.eq (v1, v2)
    | eq (BOUND m, BOUND n) = m = n
    | eq (ABS (_, e1), ABS (_, e2)) = eq (e1, e2)
    | eq (APP (p1, es1), APP (p2, es2)) =
        Operator.eq (p1, p2) andalso VectorUtil.pair_all_eq eq (es1, es2)
    | eq (_, _) = false

end
