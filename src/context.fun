functor Context (V : VARIABLE) :> CONTEXT where type name = V.t =
struct

  structure Tel = Telescope (V)
  type name = V.t

  type 'a context = ('a * Visibility.t) Tel.telescope

  val empty = Tel.empty
  fun insert H k vis v =
    Tel.snoc H (k, (v, vis))

  val interpose_after = Tel.interpose_after
  val fresh = Tel.fresh

  exception NotFound of name

  fun modify (ctx : 'a context) (k : V.t) f =
    Tel.modify ctx (k, fn (a, vis) => (f a, vis))

  fun lookup_visibility (ctx : 'a context) k =
    (Tel.lookup ctx k)

  fun lookup ctx k = #1 (lookup_visibility ctx k)

  fun search ctx phi =
    case Tel.search ctx (phi o #1) of
         SOME (lbl, (a, vis)) => SOME (lbl, a)
       | NONE => NONE

  fun list_items ctx =
    let
      open Tel.SnocView
      fun go Empty r = r
        | go (Snoc (tele', lbl, (a, vis))) r = go (out tele') ((lbl, vis, a) :: r)
    in
      go (out ctx) []
    end

  fun map f ctx =
    Tel.map ctx (fn (a, vis) => (f a, vis))

  fun map_after k f ctx =
    Tel.map_after ctx (k, fn (a, vis) => (f a, vis))

  fun to_string f tele =
    let
      open Tel.ConsView
      fun go Empty r = r
        | go (Cons (lbl, (a, vis), tele')) r =
            let
              val pretty_lbl =
                case vis of
                     Visibility.Visible => V.to_string lbl
                   | Visibility.Hidden => "[" ^ V.to_string lbl ^ "]"
            in
              go (out tele') (r ^ "\n" ^ pretty_lbl ^ " : " ^ f a)
            end
    in
      go (out tele) "·"
    end

  fun eq test =
    Tel.eq (fn ((a, vis), (b, vis')) => vis = vis' andalso test (a, b))
  fun subcontext test =
    Tel.subtelescope (fn ((a, vis), (b, vis')) => vis = vis' andalso test (a, b))
end

structure Context = Context(Syntax.Variable)
