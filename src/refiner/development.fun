functor Development
  (structure Syntax : ABT_UTIL
   structure Sequent : SEQUENT
     where type term = Syntax.t
   structure Lcf : LCF
     where type evidence = Syntax.t
     where type goal = Sequent.sequent
   structure PatternCompiler : PATTERN_COMPILER
     where type PatternTerm.t = Syntax.t
     where type PatternTerm.Operator.t = Syntax.Operator.t
   structure Extract : EXTRACT
     where type evidence = Lcf.evidence
     where type term = Syntax.t
   structure Builtins : BUILTINS
     where type Conv.term = Syntax.t
     where type operator = Syntax.Operator.t
   val goalToString : Lcf.goal -> string) : DEVELOPMENT =
struct
  structure Lcf = Lcf
  structure Telescope = Telescope(Label)
  structure PatternCompiler = PatternCompiler

  type label = Telescope.label
  type term = Syntax.t
  type judgement = Lcf.goal
  type evidence = Lcf.evidence
  type tactic = Lcf.tactic
  type operator = Syntax.Operator.t

  type conv = term -> term

  structure Object =
  struct
    type theorem =
      {statement : judgement,
       script : tactic,
       evidence : evidence Susp.susp,
       operator : Syntax.Operator.t}

    type operator_definition = PatternCompiler.rule * conv Susp.susp
    type operator_decl =
      {operator : Syntax.Operator.t,
       conversion : operator_definition option,
       notation : Notation.t option,
       userDefined : bool}

    datatype t =
        THEOREM of theorem
      | TACTIC of tactic
      | OPERATOR of operator_decl

    fun toString (lbl, THEOREM {statement, evidence,...}) =
          let
            val evidence' = Susp.force evidence
          in
            "Theorem " ^ Label.toString lbl
              ^ " : ⸤" ^ goalToString statement ^ "⸥ {\n  "
              ^ Syntax.toString evidence' ^ "\n} ext {\n  "
              ^ Syntax.toString (Extract.extract evidence') ^ "\n}."
          end
      | toString (lbl, TACTIC _) =
          "Tactic " ^ Label.toString lbl ^ "."
      | toString (lbl, OPERATOR {operator, conversion, notation, userDefined}) =
          let
            val arityDecl =
              case userDefined of
                    true => ["Operator " ^ Label.toString lbl
                            ^ " : " ^ Arity.toString (Syntax.Operator.arity operator)
                            ^ "."]
                  | false => []
            val definitionDecl =
              case conversion of
                    NONE => []
                  | SOME ({definiendum, definiens}, _) =>
                       ["⸤" ^ Syntax.toString definiendum ^ "⸥ ≝ "
                       ^ "⸤" ^ Syntax.toString definiens ^ "⸥."]

            val notationDecl =
              case notation of
                    NONE => []
                  | SOME notation =>
                       [Notation.toString notation ^ " ≝ "
                       ^ Label.toString lbl ^ "."]

            val lines = arityDecl @ definitionDecl @ notationDecl
            fun intercalate (sep, xs) =
              getOpt (foldl (fn (x, NONE) => SOME x | (x, SOME r) => SOME (r ^ sep ^ x)) NONE xs, "")
          in
            intercalate ("\n", arityDecl @ definitionDecl @ notationDecl)
          end
  end

  type object = Object.t
  type world = object Telescope.telescope
  fun enumerate t = t

  fun enumerateOperators t =
    let
      open Telescope.SnocView
      fun go Empty bind = bind
        | go (Snoc (rest, lbl, Object.OPERATOR {operator, notation, ...})) bind =
          go (out rest) ((lbl, operator, notation) :: bind)
        | go (Snoc (rest, lbl, Object.THEOREM {operator,...})) bind =
          go (out rest) ((lbl, operator, NONE) :: bind)
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

  fun prove T (lbl, theta, goal, tac) =
    let
      val (subgoals, validation) = tac goal
    in
      case subgoals of
           [] => Telescope.snoc T (lbl, Object.THEOREM
                  {operator = theta,
                   statement = goal,
                   script = tac,
                   evidence = Susp.delay (fn _ => validation [])})
         | _ => raise Fail "Subgoals not discharged"
    end

  fun defineTactic T (lbl, tac) =
    Telescope.snoc T (lbl, Object.TACTIC tac)

  fun declareOperator T (lbl, operator) =
    Telescope.snoc T
      (lbl, Object.OPERATOR
        {operator = operator,
         conversion = NONE,
         notation = NONE,
         userDefined = true})

  fun searchObject T lbl =
    let
      open Telescope.SnocView
      open Sequent
      infix >>

      fun termHasLbl lbl term =
        List.exists (fn oper => Syntax.Operator.toString oper = lbl)
                    (Syntax.operators term)
      fun evidenceHasLbl lbl term =
        List.exists (fn oper => Syntax.Operator.toString oper = lbl)
                    (Syntax.operators (Susp.force term))

      fun contains lbl (Object.THEOREM {statement = H >> P, evidence, ...}) =
          termHasLbl lbl P
          orelse evidenceHasLbl lbl evidence
          orelse Option.isSome (Context.search H (termHasLbl lbl))
        | contains lbl (Object.OPERATOR {conversion, ...}) =
          Option.getOpt (Option.map (fn ({definiendum, definiens}, _) =>
                                        termHasLbl lbl definiens)
                                    conversion,
                         false)
        | contains lbl (Object.TACTIC _) = false


      fun go Empty found = found
        | go (Snoc (rest, lbl', obj)) found =
          if contains lbl obj
          then go (out rest) ((lbl', obj) :: found)
          else go (out rest) found
    in
      go (out T) []
    end

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
        val Syntax.$ (oper, _) = Syntax.out definiendum
        val lbl = Syntax.Operator.toString oper
        val LFVs = Syntax.freeVariables definiendum
        val RFVs = Syntax.freeVariables definiens
        val _ =
          if subset (RFVs, LFVs) then
            ()
          else
            raise Fail "FV(Definiens) must be a subset of FV(Definiendum)"
        val conversion = SOME (rule, Susp.delay (fn _ => PatternCompiler.compile rule))
      in
        case Telescope.find T lbl of
             SOME (Object.OPERATOR {operator, conversion = NONE,notation, userDefined = true}) =>
               Telescope.modify T (lbl, fn _ =>
                 Object.OPERATOR
                  {operator = operator,
                   conversion = conversion,
                   notation = notation,
                   userDefined = true})
           | SOME _ => raise Subscript
           | NONE => raise Fail "Cannot define undeclared operator"
      end

    fun declareNotation T (theta, notation) =
      let
        val lbl = Syntax.Operator.toString theta
      in
        case Telescope.find T lbl of
             SOME (Object.OPERATOR {operator, conversion, notation = NONE, userDefined}) =>
               Telescope.modify T (lbl, fn _ =>
                 Object.OPERATOR
                  {operator = operator,
                   conversion = conversion,
                   notation = SOME notation,
                   userDefined = userDefined})
           | SOME _ => raise Fail "Cannot redefined notation"
           | NONE =>
               Telescope.snoc T (lbl,
                 Object.OPERATOR
                  {operator = theta,
                   conversion = NONE,
                   notation = SOME notation,
                   userDefined = false})
      end
  end


  fun lookupDefinition T theta =
    case SOME (Builtins.unfold theta) handle _ => NONE of
         NONE =>
           (case Telescope.lookup T (Syntax.Operator.toString theta) of
                 Object.OPERATOR {conversion = SOME (_, conv),...} => Susp.force conv
               | _ => raise Subscript)
       | SOME conv => conv

  fun lookupTheorem T theta =
    case Telescope.lookup T (Syntax.Operator.toString theta) of
         Object.THEOREM {statement,evidence,...} => {statement = statement, evidence = evidence}
       | _ => raise Subscript

  fun lookupExtract T theta =
    let
      val {evidence,...} = lookupTheorem T theta
    in
      Extract.extract (Susp.force evidence)
    end

  fun lookupTactic T lbl =
    case Telescope.lookup T lbl of
         Object.TACTIC tac => tac
       | _ => raise Subscript

  fun lookupObject T theta =
    case SOME (Builtins.unfold theta) handle _ => NONE of
         NONE => Telescope.lookup T (Syntax.Operator.toString theta)
       | SOME conv =>
           let
             val pattern = PatternCompiler.PatternTerm.patternForOperator theta
             val rule : PatternCompiler.rule =
               {definiendum = pattern,
                definiens = conv pattern}
           in
             Object.OPERATOR
               {operator = theta,
                conversion = SOME (rule, Susp.delay (fn () => conv)),
                notation = NONE,
                userDefined = false}
           end
end

structure Development : DEVELOPMENT =
  Development
    (structure Syntax = Syntax
     structure Sequent = Sequent
     structure PatternCompiler = PatternCompiler
     structure Extract = Extract
     structure Lcf = Lcf
     structure Builtins = Builtins

     val goalToString = Sequent.toString)
