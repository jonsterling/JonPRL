functor Development
  (structure Syntax : ABT_UTIL
     where type Operator.t = UniversalOperator.t
   structure Sequent : SEQUENT
     where type term = Syntax.t
     where Context.Syntax = Syntax
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

  structure Coq = Coq(structure Syntax = Syntax structure Sequent = Sequent)

  structure Object =
  struct
    type theorem =
      {statement : judgement,
       script : tactic,
       evidence : evidence Susp.susp,
       operator : Syntax.Operator.t}

    (* Given a theorem (evidence and the statement), generate a Coq proof. *)
    fun theorem2Coq (th : theorem) : string =
      let val {statement, script, evidence, operator} = th
	  val evidence' : Syntax.t = Susp.force evidence
      in Coq.toCoq statement evidence'
      end

    type operator_definition = PatternCompiler.rule * conv Susp.susp
    type operator_decl =
      {operator : Syntax.Operator.t,
       conversion : operator_definition option,
       notation : Notation.t option,
       userDefined : bool}

    datatype 'w t =
        THEOREM of theorem
      | TACTIC of 'w -> tactic
      | OPERATOR of operator_decl

    fun toCoq (THEOREM th) = theorem2Coq th
      | toCoq (TACTIC _) = ""
      | toCoq (OPERATOR _) = ""

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

  datatype world = World of {context : object Telescope.telescope,
                             resources : tactic list ResourcePool.dict}
  withtype object = world Object.t

  fun world2string (w : world) : string =
    case w of
	World {context, resources} =>
	Telescope.toString (fn obj => Object.toString ("",obj)) context

  fun lookupDefinition (World {context = T, resources}) theta =
    case SOME (Builtins.unfold theta) handle _ => NONE of
        NONE =>
	let val str = Syntax.Operator.toString theta
	in case Telescope.lookup T str of
               Object.OPERATOR {conversion = SOME (_, conv),...} => Susp.force conv
             | _ => raise Subscript
	end
      | SOME conv => conv

  structure Conversionals = Conversionals (structure Syntax = Syntax structure Conv = Conv(Syntax))

  fun unfoldStatement (world : world) (term : Syntax.t) =
    let val operators = Syntax.operators term
	val term' =
	    foldl (fn (theta, t) =>
		      let (*val _ = print ("(" ^ Syntax.Operator.toString theta ^ ")")*)
			  val conv = Conversionals.CDEEP (lookupDefinition world theta)
			  (*val _ = print "(found conversion)"*)
		      in conv t
		      end
		      handle E => ((*print "lookupDefinition error\n";*) t))
		  term
		  operators
	(*val _ = print ("unfolded term: " ^ Syntax.toString term' ^ "\n")*)
    in if Syntax.eq (term, term')
       then term' (* no progress *)
       else unfoldStatement world term'
    end

  fun unfoldForCoq world (thm as Object.THEOREM th) =
    let val {statement as Sequent.>> (H, P), script, evidence, operator} = th
	(*val _ = print ("unfolding term: " ^ Syntax.toString P ^ "\n")*)
	val P' = unfoldStatement world P
	val E' = Susp.delay (fn () => unfoldStatement world (Susp.force evidence))
    in Object.THEOREM {statement = Sequent.>> (H, P'),
		       script    = script,
		       evidence  = E',
		       operator  = operator}
    end
    | unfoldForCoq world (tac as Object.TACTIC _) = tac
    | unfoldForCoq world (opr as Object.OPERATOR _) = opr

  fun world2Coq (w : world) : string =
    (print ("world:\n" ^ world2string w ^ "\n------------------------------\n");
     case w of
	 World {context, resources} =>
	 Telescope.toString
	     (fn obj =>
		 (* WARNING: For now I need to unfold everything in the sequent
		  * because abstractions are not part of the theory
		  *)
		 Object.toCoq (unfoldForCoq w obj))
	     context)
    handle E =>
	   ((case E of
		 Coq.TODO msg => print ("world2Coq:TODO: " ^ msg)
	       | Coq.Malformed msg => print ("world2Coq:Malformed: " ^ msg)
	       | _ => ());
	    raise E)

  fun enumerate (World {context, resources}) = context

  fun enumerateOperators (World {context = t, resources}) =
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

  fun enumerateTactics (World {context = t, resources}) =
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

  fun enumerateResources (World {context, resources}) = ResourcePool.domain resources

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
      World {context = Telescope.empty, resources = resources}
    end

  fun prove (World {context = T, resources}) (lbl, theta, goal, tac) =
    let
      val (subgoals, validation) = tac (Goal.|: (Goal.MAIN, goal))
    in
      case subgoals of
          [] => World {context =
                        Telescope.snoc T (lbl, Object.THEOREM
                        {operator = theta,
                         statement = goal,
                         script = tac,
                         evidence = Susp.delay (fn _ => validation [])}),
                      resources = resources}
        | _ => raise Fail "Subgoals not discharged"
    end

  fun defineTactic (World {context, resources}) (lbl, tac) =
      World {context = Telescope.snoc context (lbl, Object.TACTIC tac),
             resources = resources}

  fun declareOperator (World {context, resources}) (lbl, operator) =
    World {context = Telescope.snoc context
                       (lbl, Object.OPERATOR
                               {operator = operator,
                                conversion = NONE,
                                notation = NONE,
                                userDefined = true}),
           resources = resources}

  fun searchObject (World {context = T, resources}) lbl =
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
    fun defineOperator (World {context = T, resources}) (rule as {definiendum, definiens}) =
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
               World {context = Telescope.modify T (lbl, fn _ =>
                                  Object.OPERATOR
                                    {operator = operator,
                                     conversion = conversion,
                                     notation = notation,
                                     userDefined = true}),
                      resources = resources}
           | SOME _ => raise Subscript
           | NONE => raise Fail "Cannot define undeclared operator"
      end

    fun declareNotation (World {context = T, resources}) (theta, notation) =
      let
        val lbl = Syntax.Operator.toString theta
      in
        case Telescope.find T lbl of
             SOME (Object.OPERATOR {operator, conversion, notation = NONE, userDefined}) =>
               World {context = Telescope.modify T (lbl, fn _ =>
                                  Object.OPERATOR
                                    {operator = operator,
                                     conversion = conversion,
                                     notation = SOME notation,
                                     userDefined = userDefined}),
                      resources = resources}
           | SOME _ => raise Fail "Cannot redefined notation"
           | NONE =>
               World {context = Telescope.snoc T (lbl,
                                  Object.OPERATOR
                                    {operator = theta,
                                     conversion = NONE,
                                     notation = SOME notation,
                                     userDefined = false}),
                      resources = resources}
      end
  end

  fun declareResource (World {context, resources}) r =
    World {context = context,
           resources = ResourcePool.insert resources r []}


  fun addResource (World {context, resources}) (r, t) =
    World {context = context,
           resources = ResourcePool.insertMerge resources r [t] (fn ts => t :: ts)}

  fun lookupTheorem (World {context = T, resources}) theta =
    case Telescope.lookup T (Syntax.Operator.toString theta) of
         Object.THEOREM {statement,evidence,...} => {statement = statement, evidence = evidence}
       | _ => raise Subscript

  fun lookupExtract w theta =
    let
      val {evidence,...} = lookupTheorem w theta
    in
      Extract.extract (Susp.force evidence)
    end

  fun lookupTactic (D as (World {context = T, resources})) lbl =
    case Telescope.lookup T lbl of
         Object.TACTIC tac => tac D
       | _ => raise Subscript

  fun lookupObject (World {context = T, resources}) theta =
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

  fun lookupResource (World {context, resources}) r =
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
