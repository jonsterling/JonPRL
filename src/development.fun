functor Development
  (structure Syntax : ABT_UTIL
   structure Lcf : LCF
    where type evidence = Syntax.t
   structure ConvCompiler : CONV_COMPILER
   sharing ConvCompiler.Syntax = Syntax
   structure Extract : EXTRACT
    where type evidence = Lcf.evidence
    where type term = Syntax.t
   structure Telescope : TELESCOPE
   sharing Telescope.Label = Syntax.Variable
   val as_custom_operator : Syntax.Operator.t -> Telescope.label) : DEVELOPMENT =
struct
  structure Lcf = Lcf
  structure Telescope = Telescope
  structure ConvCompiler = ConvCompiler

  type label = Telescope.label
  type term = Syntax.t

  structure Object =
  struct
    type theorem =
      {statement : Lcf.goal,
       script : Lcf.tactic,
       evidence : Lcf.evidence Susp.susp}
    type operator_decl =
      {arity : int vector,
       conversion : (ConvCompiler.rule * (ConvCompiler.conv Susp.susp)) option}

    datatype t =
        Theorem of theorem
      | Tactic of Lcf.tactic
      | Operator of operator_decl

    fun arity_to_string v =
      "(" ^ Vector.foldri (fn (i, s1, s2) => if i = (Vector.length v - 1) then s1 else s1 ^ "; " ^ s2) "" (Vector.map Int.toString v) ^ ")"

    fun to_string (lbl, Theorem {statement, evidence,...}) =
          let
            val evidence' = Susp.force evidence
          in
            "Theorem " ^ Telescope.Label.to_string lbl
              ^ " : ⸤" ^ Lcf.goal_to_string statement ^ "⸥ {\n  "
              ^ Syntax.to_string evidence' ^ "\n} ext {\n  "
              ^ Syntax.to_string (Extract.extract evidence') ^ "\n}."
          end
      | to_string (lbl, Tactic _) =
          "Tactic " ^ Telescope.Label.to_string lbl ^ "."
      | to_string (lbl, Operator {arity, conversion}) =
          "Operator " ^ Telescope.Label.to_string lbl
            ^ " : " ^ arity_to_string arity
            ^ "."
            ^ (case conversion of
                   NONE => ""
                  | SOME ({definiendum, definiens}, _) =>
                       "\n⸤" ^ Syntax.to_string definiendum ^ "⸥ ≝ "
                       ^ "⸤" ^ Syntax.to_string definiens ^ "⸥.")
  end

  type object = Object.t
  type t = object Telescope.telescope
  fun out t = t

  val empty = Telescope.empty

  exception RemainingSubgoals of Lcf.goal list

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
    Telescope.snoc T (lbl, Object.Operator {arity = arity, conversion = NONE})

  local
    open Syntax
    infix $
  in
    fun rule_get_label {definiendum, definiens} =
      case out definiendum of
           operator $ _ => as_custom_operator operator
         | _ => raise Fail "invalid rewrite rule"
  end

  fun define_operator T rule =
    let
      val lbl = rule_get_label rule
    in
      case Telescope.lookup T lbl of
           Object.Operator {arity,conversion = NONE} =>
             Telescope.modify T (lbl, fn _ =>
               Object.Operator
                {arity = arity,
                 conversion = SOME (rule, Susp.delay (fn _ => ConvCompiler.compile rule))})
         | _ => raise Subscript
    end

  fun lookup_definition T lbl =
    case Telescope.lookup T lbl of
         Object.Operator {conversion = SOME (_, conv),...} => Susp.force conv
       | Object.Theorem {evidence,...} => Syntax.subst (Extract.extract (Susp.force evidence)) lbl
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
         Object.Operator {arity,...} => arity
       | _ => raise Subscript
end

structure Development : DEVELOPMENT = Development
  (structure Syntax = Syntax
   structure ConvCompiler = ConvCompiler
   structure Extract = Extract
   structure Telescope = Telescope(StringVariable)
   structure Lcf = Lcf

   open OperatorType

   fun as_custom_operator (CUSTOM {label,...}) = label
     | as_custom_operator _ = raise Fail "not a custom operator")

