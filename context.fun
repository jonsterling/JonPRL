functor Context (V : VARIABLE) :> CONTEXT where type name = V.t =
struct

  structure Telescope = Telescope (V)
  type name = V.t

  type 'a context = ('a * Visibility.t) Telescope.telescope

  val empty = Telescope.empty
  fun insert H k vis v =
    Telescope.snoc H (k, (v, vis))

  val interpose_after = Telescope.interpose_after
  val fresh = Telescope.fresh

  exception NotFound of name

  fun modify (ctx : 'a context) (k : V.t) f =
    Telescope.modify ctx (k, fn (a, vis) => (f a, vis))

  fun lookup_visibility (ctx : 'a context) k =
    (Telescope.lookup ctx k)

  fun lookup ctx k = #1 (lookup_visibility ctx k)

  fun search ctx phi =
    case Telescope.search ctx (phi o #1) of
         SOME (lbl, (a, vis)) => SOME (lbl, a)
       | NONE => NONE

  fun list_items ctx =
    let
      open Telescope.SnocView
      fun go Empty r = r
        | go (Snoc (tele', lbl, (a, vis))) r = go (out tele') ((lbl, vis, a) :: r)
    in
      go (out ctx) []
    end

  fun map f ctx =
    Telescope.map ctx (fn (a, vis) => (f a, vis))

  fun map_after k f ctx =
    Telescope.map_after ctx (k, fn (a, vis) => (f a, vis))

  fun to_string f tele =
    let
      open Telescope.ConsView
      fun go Empty r = r
        | go (Cons (lbl, (a, vis), tele')) r =
            let
              val pretty_lbl =
                case vis of
                     Visibility.Visible => V.to_string lbl
                   | Visibility.Hidden => "[" ^ V.to_string lbl ^ "]"
            in
              go (out tele') (r ^ ", " ^ pretty_lbl ^ " : " ^ f a)
            end
    in
      go (out tele) "·"
    end

  fun eq test =
    Telescope.eq (fn ((a, vis), (b, vis')) => vis = vis' andalso test (a, b))
  fun subcontext test =
    Telescope.subtelescope (fn ((a, vis), (b, vis')) => vis = vis' andalso test (a, b))
end

structure Context = Context(Syntax.Variable)
