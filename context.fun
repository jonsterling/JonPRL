functor Context (V : VARIABLE) :> CONTEXT where Name = V =
struct
  structure M = BinaryMapFn
    (struct type ord_key = V.t
     val compare = V.compare end)

  structure Name = V
  type name = Name.t

  type 'a context = ('a * Visibility.t * int) M.map
  structure Key = M.Key

  val empty = M.empty

  fun fresh (ctx, k) =
    case M.find (ctx, k) of
         NONE => k
       | _ => fresh (ctx, Name.prime k)

  fun insert ctx k vis v =
    case M.find (ctx, k) of
         NONE => M.insert (ctx, k, (v, vis, M.numItems ctx))
       | _ => raise Fail "Name already bound"

  fun remove (ctx : 'a context) (k : V.t) =
    let
      val (ctx', (a, _, _)) = M.remove (ctx, k)
    in
      (ctx', a)
    end

  exception NotFound of name

  fun modify (ctx : 'a context) (k : V.t) f =
    case M.find (ctx, k) of
         NONE => raise NotFound k
       | SOME (a, vis, i) => M.insert (ctx, k, (f a, vis, i))

  fun lookup_visibility ctx k =
    case M.find (ctx, k) of
         SOME (v, vis, _) => (v, vis)
       | NONE => raise NotFound k

  fun lookup ctx k = #1 (lookup_visibility ctx k)

  val list_items : 'a context -> (V.t * Visibility.t * 'a) list = fn ctx =>
    List.map (fn (v, (a, vis, _)) => (v, vis, a))
     ((ListMergeSort.sort (fn ((_, (_, _, i)), (_, (_, _, j))) => i > j))
      (M.listItemsi ctx))

  (* Needs to be made more lazy *)
  fun search (ctx : 'a context) p = list_search (M.listItemsi ctx) p
  and list_search xs p =
    case xs of
      nil => NONE
    | ((i,(x, _, _)) :: ys) => if p x then SOME (i,x) else list_search ys p

  fun map f = M.map (fn (a, vis, i) => (f a, vis, i))

  fun map_after x f H =
    case M.find (H, x) of
         NONE => raise NotFound x
       | SOME (a, _, i) =>
           M.map (fn (b, vis, j) => if j < i then (f b, vis, j) else (b, vis, j)) H

  fun to_string (mode, printer) =
    let
      fun var_to_string (x, Visibility.Visible) = V.to_string mode x
        | var_to_string (x, Visibility.Hidden) = "[" ^ V.to_string mode x ^ "]"

      fun go ((x, vis, a), r) =
        r ^ ", " ^ var_to_string (x, vis) ^ " : " ^ printer mode a
    in
      foldl go "◊" o list_items
    end

  fun subcontext test (G, G') =
    let
      fun probe (x, (a, visa, _), r) =
        case M.find (G', x) of
             SOME (b, visb, _) => r andalso test (a,b) andalso visa = visb
           | NONE => false
    in
      M.foldli probe true G
    end

  fun eq test (G, G') =
    subcontext test (G, G')
      andalso
        subcontext test (G', G)
end
