functor Development
  (structure Syntax : ABT_UTIL
   structure Lcf : LCF
    where type evidence = Syntax.t
   structure Extract : EXTRACT
    where type evidence = Lcf.evidence
    where type term = Syntax.t
   structure Telescope : TELESCOPE) : DEVELOPMENT =
struct
  structure Lcf = Lcf
  structure Telescope = Telescope

  type label = Telescope.label
  type term = Syntax.t

  structure Object =
  struct
    type definition =
      {definiens : term}
    type theorem =
      {statement : Lcf.goal,
       script : Lcf.tactic,
       evidence : Lcf.evidence Susp.susp}
    type operator_decl =
      {arity : int vector}

    datatype t =
        Definition of definition
      | Theorem of theorem
      | Tactic of Lcf.tactic
      | Operator of operator_decl

    fun arity_to_string v =
      "(" ^ Vector.foldri (fn (i, s1, s2) => if i = (Vector.length v - 1) then s1 else s1 ^ "; " ^ s2) "" (Vector.map Int.toString v) ^ ")"

    fun to_string (lbl, Definition {definiens}) =
          Telescope.Label.to_string lbl ^ " =def= ⌊" ^ Syntax.to_string definiens ^ "⌋."
      | to_string (lbl, Theorem {statement, evidence,...}) =
          let
            val evidence' = Susp.force evidence
          in
            "Theorem " ^ Telescope.Label.to_string lbl
              ^ " : ⌊" ^ Lcf.goal_to_string statement ^ "⌋ {\n  "
              ^ Syntax.to_string evidence' ^ "\n} ext {\n  "
              ^ Syntax.to_string (Extract.extract evidence') ^ "\n}."
          end
      | to_string (lbl, Tactic _) =
          "Tactic " ^ Telescope.Label.to_string lbl ^ "."
      | to_string (lbl, Operator {arity}) =
          "Operator " ^ Telescope.Label.to_string lbl
            ^ " : " ^ arity_to_string arity
            ^ "."
  end

  type object = Object.t
  type t = object Telescope.telescope
  fun out t = t

  val empty = Telescope.empty

  exception RemainingSubgoals of Lcf.goal list

  fun define T (lbl, tm) =
    Telescope.snoc T (lbl, Object.Definition {definiens = tm})

  fun prove T (lbl, goal, tac) =
    let
      val (subgoals, validation) = tac goal
    in
      case subgoals of
           [] => Telescope.snoc T (lbl, Object.Theorem
                  {statement = goal,
                   script = tac,
                   evidence = Susp.delay (fn _ => validation [])})
         | _ => raise RemainingSubgoals subgoals
    end

  fun define_tactic T (lbl, tac) =
    Telescope.snoc T (lbl, Object.Tactic tac)

  fun declare_operator T (lbl, arity) =
    Telescope.snoc T (lbl, Object.Operator {arity = arity})

  fun lookup_definition T lbl =
    case Telescope.lookup T lbl of
         Object.Definition {definiens} => definiens
       | Object.Theorem {evidence,...} => Extract.extract (Susp.force evidence)
       | _ => raise Subscript

  fun lookup_theorem T lbl =
    case Telescope.lookup T lbl of
         Object.Theorem {statement,evidence,...} => {statement = statement, evidence = evidence}
       | _ => raise Subscript

  fun lookup_tactic T lbl =
    case Telescope.lookup T lbl of
         Object.Tactic tac => tac
       | _ => raise Subscript

  fun lookup_operator T lbl =
    case Telescope.lookup T lbl of
         Object.Operator {arity} => arity
       | _ => raise Subscript
end

structure Development : DEVELOPMENT = Development
  (structure Syntax = Syntax
   structure Extract = Extract
   structure Telescope = Telescope(StringVariable)
   structure Lcf = Lcf)
