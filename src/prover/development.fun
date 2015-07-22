functor Development
  (structure Syntax : ABT_UTIL
   structure Evidence : ABT_UTIL
   structure PatternSyntax : ABT_UTIL
   structure Lcf : LCF
     where type evidence = Evidence.t
   structure PatternCompiler : PATTERN_COMPILER
     where type term = Syntax.t
   structure Extract : EXTRACT
     where type evidence = Lcf.evidence
     where type term = Syntax.t
   structure Telescope : TELESCOPE
   sharing type PatternCompiler.pattern = PatternSyntax.t
   sharing type PatternSyntax.Variable.t = Syntax.Variable.t
   sharing type PatternSyntax.Operator.t = Syntax.Operator.t
   val operatorToLabel : Syntax.Operator.t -> Telescope.label
   val goalToString : Lcf.goal -> string) : DEVELOPMENT =
struct
  structure Lcf = Lcf
  structure Telescope = Telescope
  structure PatternCompiler = PatternCompiler

  type label = Telescope.label
  type term = Syntax.t
  type pattern = PatternSyntax.t
  type judgement = Lcf.goal
  type evidence = Lcf.evidence
  type tactic = Lcf.tactic

  type conv = term -> term

  structure Object =
  struct
    type theorem =
      {statement : judgement,
       script : tactic,
       evidence : evidence Susp.susp}

    type operator_definition = PatternCompiler.rule * conv Susp.susp
    type operator_decl =
      {arity : Arity.t,
       conversion : operator_definition option}

    fun operatorDeclArity {arity,conversion} = arity

    datatype t =
        THEOREM of theorem
      | TACTIC of tactic
      | OPERATOR of operator_decl

    fun arity_toString v =
      "(" ^ Vector.foldri (fn (i, s1, s2) => if i = (Vector.length v - 1) then s1 else s1 ^ "; " ^ s2) "" (Vector.map Int.toString v) ^ ")"

    fun toString (lbl, THEOREM {statement, evidence,...}) =
          let
            val evidence' = Susp.force evidence
          in
            "Theorem " ^ Telescope.Label.toString lbl
              ^ " : ⸤" ^ goalToString statement ^ "⸥ {\n  "
              ^ Evidence.toString evidence' ^ "\n} ext {\n  "
              ^ Syntax.toString (Extract.extract evidence') ^ "\n}."
          end
      | toString (lbl, TACTIC _) =
          "Tactic " ^ Telescope.Label.toString lbl ^ "."
      | toString (lbl, OPERATOR {arity, conversion}) =
          "Operator " ^ Telescope.Label.toString lbl
            ^ " : " ^ arity_toString arity
            ^ "."
            ^ (case conversion of
                   NONE => ""
                  | SOME ({definiendum, definiens}, _) =>
                       "\n⸤" ^ PatternSyntax.toString definiendum ^ "⸥ ≝ "
                       ^ "⸤" ^ Syntax.toString definiens ^ "⸥.")
  end

  type object = Object.t
  type world = object Telescope.telescope
  fun enumerate t = t

  fun enumerateOperators t =
    let
      open Telescope.SnocView
      fun go Empty bind = bind
        | go (Snoc (rest, lbl, Object.OPERATOR {arity, ...})) bind =
          go (out rest) ((lbl, arity) :: bind)
        | go (Snoc (rest, lbl, Object.THEOREM {...})) bind =
          go (out rest) ((lbl, #[]) :: bind)
        | go (Snoc (rest, lbl, _)) bind =
          go (out rest) bind
    in
      go (out t) []
    end

  fun enumerateTactics t =
    let
      open Telescope.SnocView
      fun go Empty bind = bind
        | go (Snoc (rest, lbl, Object.TACTIC _)) bind =
          go (out rest) (lbl :: bind)
        | go (Snoc (rest, lbl, Object.THEOREM {...})) bind =
          go (out rest) bind
        | go (Snoc (rest, lbl, Object.OPERATOR {...})) bind =
          go (out rest) bind
    in
      go (out t) []
    end

  val empty = Telescope.empty

  fun prove T (lbl, goal, tac) =
    let
      val (subgoals, validation) = tac goal
    in
      case subgoals of
           [] => Telescope.snoc T (lbl, Object.THEOREM
                  {statement = goal,
                   script = tac,
                   evidence = Susp.delay (fn _ => validation [])})
         | _ => raise Fail "Subgoals not discharged"
    end

  fun defineTactic T (lbl, tac) =
    Telescope.snoc T (lbl, Object.TACTIC tac)

  fun declareOperator T (lbl, arity) =
    Telescope.snoc T (lbl, Object.OPERATOR {arity = arity, conversion = NONE})

  local
    structure Set = SplaySet(structure Elem = Syntax.Variable)
    val setFromList = foldl (fn (x,S) => Set.insert S x) Set.empty
    fun subset (xs, ys) =
      let
        val ys' = setFromList ys
      in
        foldl (fn (x,R) => R andalso Set.member ys' x) true xs
      end
  in
    fun defineOperator T (rule as {definiendum, definiens}) =
      let
        val PatternSyntax.$ (oper, _) = PatternSyntax.out definiendum
        val lbl = operatorToLabel oper
        val LFVs = PatternSyntax.freeVariables definiendum
        val RFVs = Syntax.freeVariables definiens
        val _ =
          if subset (RFVs, LFVs) then
            ()
          else
            raise Fail "FV(Definiens) must be a subset of FV(Definiendum)"
        val conversion = SOME (rule, Susp.delay (fn _ => PatternCompiler.compile rule))
      in
        case Telescope.find T lbl of
             SOME (Object.OPERATOR {arity,conversion = NONE}) =>
               Telescope.modify T (lbl, fn _ =>
                 Object.OPERATOR
                  {arity = arity,
                   conversion = conversion})
           | SOME _ => raise Subscript
           | NONE =>
               Telescope.snoc T (lbl,
                 Object.OPERATOR
                  {arity = Syntax.Operator.arity oper,
                   conversion = conversion})

      end
  end

  fun lookupDefinition T lbl =
    case Telescope.lookup T lbl of
         Object.OPERATOR {conversion = SOME (_, conv),...} => Susp.force conv
       | _ => raise Subscript

  fun lookupTheorem T lbl =
    case Telescope.lookup T lbl of
         Object.THEOREM {statement,evidence,...} => {statement = statement, evidence = evidence}
       | _ => raise Subscript

  fun lookupExtract T lbl =
    let
      val {evidence,...} = lookupTheorem T lbl
    in
      Extract.extract (Susp.force evidence)
    end

  fun lookupTactic T lbl =
    case Telescope.lookup T lbl of
         Object.TACTIC tac => tac
       | _ => raise Subscript

  fun lookupOperator T lbl =
    case Telescope.lookup T lbl of
         Object.OPERATOR {arity,...} => arity
       | Object.THEOREM {...} => #[]
       | _ => raise Subscript
end

structure Development : DEVELOPMENT =
  Development
    (structure Syntax = Syntax
     structure Evidence = Syntax
     structure PatternSyntax = PatternSyntax
     structure PatternCompiler = PatternCompiler
     structure Extract = Extract
     structure Telescope = Telescope(StringVariable)
     structure Lcf = Lcf

     val operatorToLabel = Syntax.Operator.toString
     val goalToString = Sequent.toString)
