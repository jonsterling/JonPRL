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
   val asCustomOperator : Syntax.Operator.t -> Telescope.label) : DEVELOPMENT =
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
      {arity : Arity.t,
       conversion : (ConvCompiler.rule * (ConvCompiler.conv Susp.susp)) option}

    datatype t =
        Theorem of theorem
      | Tactic of Lcf.tactic
      | Operator of operator_decl

    fun arity_toString v =
      "(" ^ Vector.foldri (fn (i, s1, s2) => if i = (Vector.length v - 1) then s1 else s1 ^ "; " ^ s2) "" (Vector.map Int.toString v) ^ ")"

    fun toString (lbl, Theorem {statement, evidence,...}) =
          let
            val evidence' = Susp.force evidence
          in
            "Theorem " ^ Telescope.Label.toString lbl
              ^ " : ⸤" ^ Lcf.goalToString statement ^ "⸥ {\n  "
              ^ Syntax.toString evidence' ^ "\n} ext {\n  "
              ^ Syntax.toString (Extract.extract evidence') ^ "\n}."
          end
      | toString (lbl, Tactic _) =
          "Tactic " ^ Telescope.Label.toString lbl ^ "."
      | toString (lbl, Operator {arity, conversion}) =
          "Operator " ^ Telescope.Label.toString lbl
            ^ " : " ^ arity_toString arity
            ^ "."
            ^ (case conversion of
                   NONE => ""
                  | SOME ({definiendum, definiens}, _) =>
                       "\n⸤" ^ Syntax.toString definiendum ^ "⸥ ≝ "
                       ^ "⸤" ^ Syntax.toString definiens ^ "⸥.")
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

  fun defineTactic T (lbl, tac) =
    Telescope.snoc T (lbl, Object.Tactic tac)

  fun declareOperator T (lbl, arity) =
    Telescope.snoc T (lbl, Object.Operator {arity = arity, conversion = NONE})

  local
    open Syntax
    infix $
  in
    fun ruleGetLabel {definiendum, definiens} =
      case out definiendum of
           operator $ _ => asCustomOperator operator
         | _ => raise Fail "invalid rewrite rule"
  end

  structure FreeVariables = AbtFreeVariables(Syntax)
  fun defineOperator T (rule as {definiendum, definiens}) =
    let
      val lbl = ruleGetLabel rule
      val LFVs = FreeVariables.freeVariables definiendum
      val RFVs = FreeVariables.freeVariables definiens
      val _ =
        if FreeVariables.Set.subset (RFVs, LFVs) then
          ()
        else
          raise Fail "FV(Definiens) must be a subset of FV(Definiendum)"
    in
      case Telescope.lookup T lbl of
           Object.Operator {arity,conversion = NONE} =>
             Telescope.modify T (lbl, fn _ =>
               Object.Operator
                {arity = arity,
                 conversion = SOME (rule, Susp.delay (fn _ => ConvCompiler.compile rule))})
         | _ => raise Subscript
    end

  fun lookupDefinition T lbl =
    case Telescope.lookup T lbl of
         Object.Operator {conversion = SOME (_, conv),...} => Susp.force conv
       | Object.Theorem {evidence,...} => (fn tm =>
           case List.find (fn v => Syntax.Variable.toString v = Telescope.Label.toString lbl) (Syntax.freeVariables tm) of
                NONE => tm
              | SOME v => Syntax.subst (Extract.extract (Susp.force evidence)) v tm)
       | _ => raise Subscript

  fun lookupTheorem T lbl =
    case Telescope.lookup T lbl of
         Object.Theorem {statement,evidence,...} => {statement = statement, evidence = evidence}
       | _ => raise Subscript

  fun lookupTactic T lbl =
    case Telescope.lookup T lbl of
         Object.Tactic tac => tac
       | _ => raise Subscript

  fun lookupOperator T lbl =
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

   fun asCustomOperator (CUSTOM {label,...}) = label
     | asCustomOperator _ = raise Fail "not a custom operator")

