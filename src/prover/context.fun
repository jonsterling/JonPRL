functor Context (Syntax : ABT_UTIL) : CONTEXT =
struct
  structure V = Syntax.Variable
  structure Syntax = Syntax
  structure Telescope = Telescope (V)
  type name = V.t
  type term = Syntax.t

  type context = (term * Visibility.t) Telescope.telescope

  val empty = Telescope.empty
  fun insert H k vis v =
    Telescope.snoc H (k, (v, vis))

  val interposeAfter = Telescope.interposeAfter
  val fresh = Telescope.fresh

  fun isEmpty (ctx : context) =
    let
      open Telescope.SnocView
    in
      case out ctx of
           Empty => true
         | _ => false
    end

  exception NotFound of name

  fun modify (ctx : context) (k : V.t) f =
    Telescope.modify ctx (k, fn (a, vis) => (f a, vis))

  fun lookupVisibility (ctx : context) k =
    (Telescope.lookup ctx k)

  fun lookup ctx k = #1 (lookupVisibility ctx k)

  fun nth ctx i =
    let
      open Telescope.ConsView
      fun go n Empty = raise Subscript
        | go n (Cons (lbl, _, tele')) =
          if n = i then lbl else go (n + 1) (out tele')
    in
      go 0 (out ctx)
    end

  fun search ctx phi =
    case Telescope.search ctx (phi o #1) of
         SOME (lbl, (a, vis)) => SOME (lbl, a)
       | NONE => NONE

  fun listItems ctx =
    let
      open Telescope.SnocView
      fun go Empty r = r
        | go (Snoc (tele', lbl, (a, vis))) r = go (out tele') ((lbl, vis, a) :: r)
    in
      go (out ctx) []
    end

  fun map f ctx =
    Telescope.map ctx (fn (a, vis) => (f a, vis))

  fun mapAfter k f ctx =
    Telescope.mapAfter ctx (k, fn (a, vis) => (f a, vis))

  fun toString tele =
    let
      open Telescope.ConsView
      fun go i Empty r = r
        | go i (Cons (lbl, (a, vis), tele')) r =
            let
              val prettyLbl =
                case vis of
                     Visibility.Visible => V.toString lbl
                   | Visibility.Hidden => "[" ^ V.toString lbl ^ "]"
            in
              go (i + 1) (out tele') (r ^ "\n" ^ Int.toString i ^ ". " ^ prettyLbl ^ " : " ^ Syntax.toString a)
            end
    in
      go 1 (out tele) ""
    end

  val eq : context * context -> bool =
    Telescope.eq (fn ((a, vis), (b, vis')) => vis = vis' andalso Syntax.eq (a, b))
  val subcontext : context * context -> bool =
    Telescope.subtelescope (fn ((a, vis), (b, vis')) => vis = vis' andalso Syntax.eq (a, b))

  exception Open of term

  fun rebind ctx tm =
    let
      open Telescope.SnocView

      fun makeVarTable vs =
        let
          fun go [] R = R
            | go (x::xs) R = go xs (StringListDict.insert R (V.toString x) x)
        in
          go vs StringListDict.empty
        end

      fun go Empty tbl tm = (tbl, tm)
        | go (Snoc (ctx', v, (a,vis))) tbl tm =
           if StringListDict.isEmpty tbl then
             (tbl, tm)
           else
             let
               val vstr = V.toString v
             in
               case StringListDict.find tbl vstr of
                    NONE =>
                      go (out ctx') tbl tm
                  | SOME v' =>
                      go (out ctx') (StringListDict.remove tbl vstr)
                      (Syntax.subst (Syntax.``v) v' tm)
             end
      val (tbl, tm') = go (out ctx) (makeVarTable (Syntax.freeVariables tm)) tm
      val () = if StringListDict.isEmpty tbl then () else raise Open tm
    in
      tm'
    end

    fun rebindName H v =
      let
        val Syntax.` v' = Syntax.out (rebind H (Syntax.`` v))
      in
        v'
      end
end

structure Context = Context(Syntax)
