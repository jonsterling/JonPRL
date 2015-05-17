functor ContextUtil
  (structure Context : CONTEXT
   structure Syntax : ABT_UTIL
   sharing Context.Name = Syntax.Variable) : CONTEXT_UTIL =
struct
  open Context
  structure Syntax = Syntax

  local
    datatype Mode = Scan | Check
    fun go _ [] x = true
      | go Scan ((y, _) :: ys) x =
        if Context.Name.eq x y
        then go Check ys x
        else go Scan ys x
      | go Check ((_, A) :: ys) x =
        not (Syntax.has_free (A, x)) andalso go Check ys x
  in
    fun is_irrelevant (H, x) =
      go Scan (list_items H) x
  end
end
