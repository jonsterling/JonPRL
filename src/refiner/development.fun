functor Development
  (structure Syntax : ABT_UTIL
   structure Sequent : SEQUENT
     where type term = Syntax.t
   structure Lcf : LCF
     where type evidence = Syntax.t
     where type goal = Sequent.sequent Goal.goal
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
  type judgement = Sequent.sequent
  type evidence = Lcf.evidence
  type tactic = Lcf.tactic
  type operator = Syntax.Operator.t
  type resource = Resource.t

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
              ^ " : ⸤" ^ Sequent.toString statement ^ "⸥ {\n  "
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
                       [Notation.toString notation ^ " := "
                       ^ Label.toString lbl ^ "."]

            val lines = arityDecl @ definitionDecl @ notationDecl
            fun intercalate (sep, xs) =
              getOpt (foldl (fn (x, NONE) => SOME x | (x, SOME r) => SOME (r ^ sep ^ x)) NONE xs, "")
          in
            intercalate ("\n", arityDecl @ definitionDecl @ notationDecl)
          end
  end

  structure ResourcePool = SplayDict
    (structure Key =
       struct
         open Resource

         fun compare (l, r) = String.compare (toString l, toString r)
         fun eq (l, r) = compare (l, r) = EQUAL
       end)

  type object = Object.t
  type world = {context : object Telescope.telescope,
                resources : tactic list ResourcePool.dict}

  fun enumerate {context, resources} = context

  fun enumerateOperators {context = t, resources} =
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

  fun enumerateTactics {context = t, resources} =
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

  fun enumerateResources {context, resources} = ResourcePool.domain resources

  val empty : world=
    let
      val resources =
        ResourcePool.insert
          (ResourcePool.insert
             (ResourcePool.insert
                (ResourcePool.insert
                   (ResourcePool.insert ResourcePool.empty Resource.AUTO [])
                   Resource.INTRO [])
                Resource.EQ_CD [])
             Resource.ELIM [])
          Resource.WF []
    in
      {context = Telescope.empty, resources = resources}
    end

  fun prove {context = T, resources} (lbl, theta, goal, tac) =
    let
      val (subgoals, validation) = tac (Goal.|: (Goal.MAIN, goal))
    in
      case subgoals of
          [] => {context =
                  Telescope.snoc T (lbl, Object.THEOREM
                  {operator = theta,
                   statement = goal,
                   script = tac,
                   evidence = Susp.delay (fn _ => validation [])}),
                resources = resources}
        | _ => raise Fail "Subgoals not discharged"
    end

  fun defineTactic {context, resources} (lbl, tac) =
      {context = Telescope.snoc context (lbl, Object.TACTIC tac),
       resources = resources}

  fun declareOperator {context, resources} (lbl, operator) =
    {context = Telescope.snoc context
                 (lbl, Object.OPERATOR
                         {operator = operator,
                          conversion = NONE,
                          notation = NONE,
                          userDefined = true}),
     resources = resources}

  fun searchObject {context = T, resources} lbl =
    let
      open Telescope.SnocView
      open Goal Sequent
      infix 3 >>

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
    fun defineOperator {context = T, resources} (rule as {definiendum, definiens}) =
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
               {context = Telescope.modify T (lbl, fn _ =>
                            Object.OPERATOR
                              {operator = operator,
                               conversion = conversion,
                               notation = notation,
                               userDefined = true}),
                resources = resources}
           | SOME _ => raise Subscript
           | NONE => raise Fail "Cannot define undeclared operator"
      end

    fun declareNotation {context = T, resources} (theta, notation) =
      let
        val lbl = Syntax.Operator.toString theta
      in
        case Telescope.find T lbl of
             SOME (Object.OPERATOR {operator, conversion, notation = NONE, userDefined}) =>
               {context = Telescope.modify T (lbl, fn _ =>
                            Object.OPERATOR
                              {operator = operator,
                               conversion = conversion,
                               notation = SOME notation,
                               userDefined = userDefined}),
                resources = resources}
           | SOME _ => raise Fail "Cannot redefined notation"
           | NONE =>
               {context = Telescope.snoc T (lbl,
                            Object.OPERATOR
                              {operator = theta,
                               conversion = NONE,
                               notation = SOME notation,
                               userDefined = false}),
                resources = resources}
      end
  end

  fun declareResource {context, resources} r =
    {context = context,
     resources = ResourcePool.insert resources r []}


  fun addResource {context, resources} (r, t) =
    {context = context,
     resources = ResourcePool.insertMerge resources r [t] (fn ts => t :: ts)}

  fun lookupDefinition {context = T, resources} theta =
    case SOME (Builtins.unfold theta) handle _ => NONE of
         NONE =>
           (case Telescope.lookup T (Syntax.Operator.toString theta) of
                 Object.OPERATOR {conversion = SOME (_, conv),...} => Susp.force conv
               | _ => raise Subscript)
       | SOME conv => conv

  fun lookupTheorem {context = T, resources} theta =
    case Telescope.lookup T (Syntax.Operator.toString theta) of
         Object.THEOREM {statement,evidence,...} => {statement = statement, evidence = evidence}
       | _ => raise Subscript

  fun lookupExtract w theta =
    let
      val {evidence,...} = lookupTheorem w theta
    in
      Extract.extract (Susp.force evidence)
    end

  fun lookupTactic {context = T, resources} lbl =
    case Telescope.lookup T lbl of
         Object.TACTIC tac => tac
       | _ => raise Subscript

  fun lookupObject {context = T, resources} theta =
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

  fun lookupResource {context, resources} r =
    ResourcePool.lookup resources r
      handle ResourcePool.Absent =>
        raise Fail ("Unknown resource " ^ Resource.toString r)
end

structure Development : DEVELOPMENT =
  Development
    (structure Syntax = Syntax
     structure Sequent = Sequent
     structure PatternCompiler = PatternCompiler
     structure Extract = Extract
     structure Lcf = Lcf
     structure Builtins = Builtins

     val goalToString = Goal.toString Sequent.toString)
