functor Context (V : VARIABLE) :> CONTEXT where type name = V.t =
struct
  structure M = BinaryMapFn
    (struct type ord_key = V.t val compare = V.compare end)

  type name = V.t

  fun list_search xs p =
    case xs of
      nil => NONE
    | ((i,x) :: ys) => if p x then SOME (i,x) else list_search ys p

  type 'a context = 'a M.map
  structure Key = M.Key

  val empty = M.empty

  fun insert ctx k v = M.insert (ctx, k, v)
  fun remove ctx k = M.remove (ctx, k)

  exception NotFound of name
  fun lookup ctx k =
    case M.find (ctx, k) of
         SOME v => v
       | NONE => raise NotFound k

  (* Needs to be made more lazy *)
  fun search ctx p = list_search (M.listItemsi ctx) p

  val map = M.map
  val mapi = M.mapi
  val foldri = M.foldri

  fun to_string (mode, printer) ctx =
    let
      fun welp (x, a, r) =
        r ^ ", " ^ V.to_string mode x ^ ":" ^ printer mode a
    in
      M.foldli welp "◊" ctx
    end

  fun subcontext test (G, G') =
    let
      fun probe (x, a, r) =
        case M.find (G', x) of
             SOME b => r andalso test (a,b)
           | NONE => false
    in
      M.foldli probe true G
    end

  fun eq test (G, G') =
    subcontext test (G, G')
      andalso
        subcontext test (G', G)
end
