structure Context :> CONTEXT where type name = Variable.t =
struct
  structure M = BinaryMapFn
    (struct type ord_key = Variable.t val compare = Variable.compare end)

  type name = Variable.t

  fun list_search xs p =
    case xs of
      nil => NONE
    | ((i,x) :: ys) => if p x then SOME (i,x) else list_search ys p

  type 'a context = 'a M.map
  structure Key = M.Key

  val empty = M.empty

  fun insert ctx k v = M.insert (ctx, k, v)
  fun remove ctx k = M.remove (ctx, k)

  fun lookup ctx k = M.find (ctx, k)

  (* Needs to be made more lazy *)
  fun search ctx p = list_search (M.listItemsi ctx) p

  val map = M.map
  val mapi = M.mapi

  fun eq test (ctx, ctx') =
    let
      fun probe (x, a, r) =
        case lookup ctx' x of
             SOME b => r andalso test (a, b)
           | NONE => false
    in
      M.foldli probe true ctx
    end
end
