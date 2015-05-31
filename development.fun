functor Development
  (structure Syntax : ABT_UTIL
   structure Lcf : LCF
   structure Telescope : TELESCOPE) : DEVELOPMENT =
struct
  structure Lcf = Lcf
  structure Telescope = Telescope

  type label = Telescope.label
  type term = Syntax.t

  type definition = {definiens : term}
  type theorem =
    {statement : Lcf.goal,
     script : Lcf.tactic,
     evidence : Lcf.evidence Susp.susp}

  datatype object =
      Definition of definition
    | Theorem of theorem

  type t = object Telescope.telescope
  fun out t = t

  val empty = Telescope.empty

  exception RemainingSubgoals of Lcf.goal list

  fun define T (lbl, tm) =
    Telescope.snoc T (lbl, Definition {definiens = tm})

  fun prove T (lbl, goal, tac) =
    let
      val (subgoals, validation) = tac goal
    in
      case subgoals of
           [] => Telescope.snoc T (lbl, Theorem
                  {statement = goal,
                   script = tac,
                   evidence = Susp.delay (fn _ => validation [])})
         | _ => raise RemainingSubgoals subgoals
    end

  fun lookup_definition T lbl =
    case Telescope.lookup T lbl of
         Definition {definiens} => definiens
       | _ => raise Subscript

  fun lookup_theorem T lbl =
    case Telescope.lookup T lbl of
         Theorem {statement,evidence,...} => {statement = statement, evidence = evidence}
       | _ => raise Subscript
end

structure Development : DEVELOPMENT = Development
  (structure Syntax = Syntax
   structure Telescope = Telescope(StringVariable)
   structure Lcf = Lcf)
