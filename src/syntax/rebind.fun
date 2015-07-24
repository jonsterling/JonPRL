(* A utility on ABTs for rebinding variables based on name *)
functor Rebind(A : ABT_UTIL) :
        sig
          val rebind : A.Variable.t list -> A.t -> A.t
        end =
struct
  open A

  fun rebind vars tm =
    let
      fun makeVarTable vs =
        let
          fun go [] R = R
            | go (x::xs) R = go xs (StringListDict.insert R (Variable.toString x) x)
        in
          go vs StringListDict.empty
        end

      fun go [] tbl tm = (tbl, tm)
        | go (v :: vars') tbl tm =
           if StringListDict.isEmpty tbl then
             (tbl, tm)
           else
             let
               val vstr = Variable.toString v
             in
               case StringListDict.find tbl vstr of
                    NONE => go vars' tbl tm
                  | SOME v' =>
                    go vars' (StringListDict.remove tbl vstr)
                       (subst (``v) v' tm)
             end
      val (tbl, tm') = go vars (makeVarTable (freeVariables tm)) tm
    in
      tm'
    end
end
