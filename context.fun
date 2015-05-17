functor Context (V : VARIABLE) :> CONTEXT where type name = V.t =
struct
  structure M = BinaryMapFn
    (struct type ord_key = V.t
     val compare = V.compare end)

  type name = V.t

  type 'a context = ('a * int) M.map
  structure Key = M.Key

  val empty = M.empty

  fun insert ctx k v =
    case M.find (ctx, k) of
         NONE => M.insert (ctx, k, (v, M.numItems ctx))
       | _ => raise Fail "variable already bound"

  fun remove (ctx : 'a context) (k : V.t) =
    let
      val (ctx', (a, _)) = M.remove (ctx, k)
    in
      (ctx', a)
    end

  exception NotFound of name
  fun lookup ctx k =
    case M.find (ctx, k) of
         SOME (v, _) => v
       | NONE => raise NotFound k

  val list_items : 'a context -> (V.t * 'a) list = fn ctx =>
    List.map (fn (v, (a, _)) => (v, a))
     ((ListMergeSort.sort (fn ((_, (_, i)), (_, (_, j))) => i > j))
      (M.listItemsi ctx))

  (* Needs to be made more lazy *)
  fun search (ctx : 'a context) p = list_search (M.listItemsi ctx) p
  and list_search xs p =
    case xs of
      nil => NONE
    | ((i,(x, _)) :: ys) => if p x then SOME (i,x) else list_search ys p

  fun map f = M.map (fn (v, i) => (f v, i))
  fun foldri f = M.foldri (fn (v, (a, i), m) => f (v, a, m))

  fun to_string (mode, printer) =
    let
      fun welp ((x, a), r) =
        r ^ ", " ^ V.to_string mode x ^ " : " ^ printer mode a
    in
      foldl welp "◊" o list_items
    end

  fun subcontext test (G, G') =
    let
      fun probe (x, (a, _), r) =
        case M.find (G', x) of
             SOME (b, _) => r andalso test (a,b)
           | NONE => false
    in
      M.foldli probe true G
    end

  fun eq test (G, G') =
    subcontext test (G, G')
      andalso
        subcontext test (G', G)
end
