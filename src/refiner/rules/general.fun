functor GeneralRules(Utils : RULES_UTIL) : GENERAL_RULES =
struct
  open Utils
  open Goal Sequent Syntax CttCalculus Derivation

  (* We need this because otherwise the [world] from
   * utils is shadowed by one in CttCalculus
   *)
  type world = Development.world

  infix $ \ BY ^!
  infix 3 >>
  infix 2 |:
  infix 8 $$ // @@
  infixr 8 \\

  fun Witness M (_ |: H >> P) =
    let
      val M = Context.rebind H M
      val _ = assertClosed H M
      val hasHiddenVariables =
        foldl
          (fn (x, b) => b orelse #2 (Context.lookupVisibility H x) = Visibility.Hidden handle _ => false)
          false
          (freeVariables M)
      val _ =
        if hasHiddenVariables then
          assertIrrelevant (H, P)
        else
          ()
    in
      [ AUX |: H >> C.`> MEM $$ #[M, P]
      ] BY (fn [D] => D.`> WITNESS $$ #[M, D]
             | _ => raise Refine)
    end

  fun HypEq (_ |: H >> P) =
    let
      val P = P
      val #[M, M', A] = P ^! EQ
      val x = asVariable (unify M M')
      val _ = unify A (Context.lookup H x)
    in
      [] BY (fn _ => D.`> HYP_EQ $$ #[`` x])
    end

  fun Unhide hyp (T |: H >> P) =
    let val z = eliminationTarget hyp (H >> P)
	val _ = P ^! EQ
	val K = Context.modifyVisibility H z (fn x => x) (fn _ => Visibility.Visible)
    in [T |: K >> P] BY mkEvidence UNHIDE
    end

  fun Hypothesis hyp (goal as _ |: S) = Hypothesis_ (eliminationTarget hyp S) goal

  fun Assumption (goal as _ |: H >> P) =
    case Context.search H (fn x => Syntax.eq (P, x)) of
         SOME (x, _) => Hypothesis_ x goal
       | NONE => raise Refine

  fun Assert (term, name) (_ |: H >> P) =
    let
      val z =
          case name of
              SOME z => z
            | NONE => Context.fresh (H, Variable.named "H")
      val term' = Context.rebind H term
    in
      [ AUX |: H >> term'
      , MAIN |: H @@ (z, term') >> P
      ] BY (fn [D, E] => D.`> ASSERT $$ #[D, z \\ E]
             | _ => raise Refine)
    end

  fun Thin hyp (_ |: H >> P) =
    let
      val z = eliminationTarget hyp (H >> P)
      val H' = Context.thin H z
    in
      [ MAIN |: H' >> P
      ] BY (fn [D] => D | _ => raise Refine)
    end

   local
     structure Unify = UnifySequent(Sequent)
   in
     fun MatchSingle (hyps, goal, body) (l |: H >> P) =
       let
         val {matched, subst} =
           Unify.unify ({hyps = hyps, goal = goal}, (H >> P))
             handle Unify.Mismatch => raise Refine
       in
         body subst (l |: H >> P)
       end
   end

   fun Fiat (_ |: H >> P) =
     [] BY (fn _ => D.`> FIAT $$ #[])

   fun RewriteGoal (c : conv) (_ |: H >> P) =
     [ MAIN |: Context.map c H >> c P
     ] BY (fn [D] => D | _ => raise Refine)

   local
     structure LevelSolver = LevelSolver (SyntaxWithUniverses (Syntax))
     structure SequentLevelSolver = SequentLevelSolver
       (structure Solver = LevelSolver
        structure Abt = Syntax
        structure Sequent = Sequent)
   in
     fun Lemma (world, theta) (_ |: H >> P) =
       let
         val {statement, evidence} = Development.lookupTheorem world theta
         val constraints = SequentLevelSolver.generateConstraints (statement, H >> P)
         val substitution = LevelSolver.Level.resolve constraints
         val shovedEvidence = LevelSolver.subst substitution (Susp.force evidence)
         val lemmaOperator = LEMMA {label = Operator.toString theta}
       in
         [] BY (fn _ => D.`> lemmaOperator $$ #[])
       end
   end

   local
     open Conversionals
     infix CTHEN
     structure LevelSolver = LevelSolver (SyntaxWithUniverses (Syntax))

     fun convTheorem theta world =
       let
         val extract = Development.lookupExtract world theta
       in
         fn M =>
           case out M of
              theta' $ #[] =>
                if Syntax.Operator.eq (theta, theta') then
                  extract
                else
                  raise Conv.Conv
            | _ => raise Conv.Conv
       end

     fun convOperator theta world =
       Development.lookupDefinition world theta
         handle Subscript => convTheorem theta world
   in
     fun Unfolds (world, thetas) (lbl |: H >> P) =
       let
         val conv =
           foldl (fn ((theta, ok), acc) =>
             let
               val k = case ok of SOME k => k | NONE => Level.base
               val levelConv = LevelSolver.subst (LevelSolver.Level.yank k)
               val conv = CDEEP (convOperator theta world CTHEN levelConv)
             in
               acc CTHEN conv
             end) CID thetas

       in
         [ lbl |: Context.map conv H >> conv P
         ] BY (fn [D] => D
                | _ => raise Refine)
       end
   end
end
