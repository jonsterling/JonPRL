functor Context (Syntax : ABT_UTIL) : CONTEXT =
struct
  structure V = Syntax.Variable
  structure Syntax = Syntax
  structure Tel = Telescope (V)
  type name = V.t
  type term = Syntax.t

  type context = (term * Visibility.t) Tel.telescope

  val empty = Tel.empty
  fun insert H k vis v =
    Tel.snoc H (k, (v, vis))

  val interpose_after = Tel.interpose_after
  val fresh = Tel.fresh

  fun is_empty (ctx : context) =
    let
      open Tel.SnocView
    in
      case out ctx of
           Empty => true
         | _ => false
    end

  exception NotFound of name

  fun modify (ctx : context) (k : V.t) f =
    Tel.modify ctx (k, fn (a, vis) => (f a, vis))

  fun lookup_visibility (ctx : context) k =
    (Tel.lookup ctx k)

  fun lookup ctx k = #1 (lookup_visibility ctx k)

  fun nth ctx i =
    let
      open Tel.ConsView
      fun go n Empty = raise Subscript
        | go n (Cons (lbl, _, tele')) =
          if n = i then lbl else go (n + 1) (out tele')
    in
      go 0 (out ctx)
    end

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

  fun to_string tele =
    let
      open Tel.ConsView
      fun go i Empty r = r
        | go i (Cons (lbl, (a, vis), tele')) r =
            let
              val pretty_lbl =
                case vis of
                     Visibility.Visible => V.to_string lbl
                   | Visibility.Hidden => "[" ^ V.to_string lbl ^ "]"
            in
              go (i + 1) (out tele') (r ^ "\n" ^ Int.toString i ^ ". " ^ pretty_lbl ^ " : " ^ Syntax.to_string a)
            end
    in
      go 1 (out tele) ""
    end

  val eq : context * context -> bool =
    Tel.eq (fn ((a, vis), (b, vis')) => vis = vis' andalso Syntax.eq (a, b))
  val subcontext : context * context -> bool =
    Tel.subtelescope (fn ((a, vis), (b, vis')) => vis = vis' andalso Syntax.eq (a, b))

  fun rebind ctx tm =
    let
      open Tel.SnocView

      fun make_var_table vs =
        let
          fun go [] R = R
            | go (x::xs) R = go xs (StringListDict.insert R (V.to_string x) x)
        in
          go vs StringListDict.empty
        end

      fun go Empty tbl tm = tm
        | go (Snoc (ctx', v, (a,vis))) tbl tm =
           if StringListDict.isEmpty tbl then
             tm
           else
             let
               val vstr = V.to_string v
             in
               case StringListDict.find tbl vstr of
                    NONE =>
                      go (out ctx') tbl tm
                  | SOME v' =>
                      go (out ctx') (StringListDict.remove tbl vstr)
                      (Syntax.subst (Syntax.``v) v' tm)
             end
    in
      go (out ctx) (make_var_table (Syntax.free_variables tm)) tm
    end
end

structure Context = Context(Syntax)
