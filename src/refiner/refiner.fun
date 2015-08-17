functor Refiner
  (structure Syntax : ABT_UTIL
     where type Operator.t = UniversalOperator.t
   structure Sequent : SEQUENT
     where type term = Syntax.t
     where Context.Syntax = Syntax
   structure Lcf : LCF
     where type evidence = Syntax.t
     where type goal = Sequent.sequent Goal.goal

   structure Development : DEVELOPMENT
     where type judgement = Sequent.sequent
     where type evidence = Lcf.evidence
     where type tactic = Lcf.tactic
     where type operator = UniversalOperator.t

   structure Conv : CONV where type term = Syntax.t
   structure Semantics : SMALL_STEP where type syn = Syntax.t
   sharing type Development.term = Syntax.t
   structure Builtins : BUILTINS
     where type Conv.term = Conv.term) : REFINER =
struct
  structure Lcf = Lcf
  structure Conv = ConvUtil(structure Conv = Conv and Syntax = Syntax)
  structure Syntax = Syntax

  structure Sequent = Sequent
  structure Development = Development

  type tactic = Lcf.tactic
  type conv = Conv.conv
  type name = Sequent.name
  type term = Syntax.t
  type goal = Sequent.sequent

  type operator = Syntax.Operator.t
  type hyp = name HypSyn.t

  type world = Development.world

  exception Refine

  structure Rules =
  struct
    structure Utils = RulesUtil
      (structure Lcf = Lcf
       structure Syntax = Syntax
       structure Conv = Conv
       structure Semantics = Semantics
       structure Sequent = Sequent
       structure Development = Development
       structure Builtins = Builtins

       exception Refine = Refine)

    open Utils
    open Goal Sequent Syntax CttCalculus Derivation

    infix $ \ BY ^!
    infix 3 >>
    infix 2 |:
    infix 8 $$ // @@
    infixr 8 \\

    structure UnivRules = UnivRules(Utils)
    open UnivRules

    structure EqRules = EqRules(Utils)
    open EqRules

    structure FunRules = FunRules(Utils)
    open FunRules

    structure ISectRules = ISectRules(Utils)
    open ISectRules

    structure SubsetRules = SubsetRules(Utils)
    open SubsetRules

    structure NatRules = NatRules(Utils)
    open NatRules

    structure BaseRules = BaseRules(Utils)
    open BaseRules

    structure ImageRules = ImageRules(Utils)
    open ImageRules

    structure GeneralRules = GeneralRules(Utils)
    open GeneralRules

    structure ProdRules = ProdRules(Utils)
    open ProdRules

    structure PlusRules = PlusRules(Utils)
    open PlusRules

    fun AtomEq (_ |: H >> P) =
      let
        val #[atm, atm', uni] = P ^! EQ
        val #[] = atm ^! ATOM
        val #[] = atm' ^! ATOM
        val (UNIV _, _) = asApp uni
      in
        [] BY mkEvidence ATOM_EQ
      end

    fun TokenEq (_ |: H >> P) =
      let
        val #[tok, tok', atm] = P ^! EQ
        val #[] = atm ^! ATOM
        val (TOKEN s1, _) = asApp tok
        val (TOKEN s2, _) = asApp tok'
        val true = s1 = s2
      in
        [] BY mkEvidence TOKEN_EQ
      end


  fun TestAtomEq oz (_ |: H >> P) =
    let
      val #[match1, match2, T] = P ^! EQ
      val #[u1, v1, s1, t1] = match1 ^! TEST_ATOM
      val #[u2, v2, s2, t2] = match2 ^! TEST_ATOM
      val z = Context.fresh (H, case oz of NONE => Variable.named "z" | SOME z => z)
      val atm = C.`> ATOM $$ #[]
      val u1v1 = C.`> EQ $$ #[u1, v1, atm]
      val u1v1' = C.`> NOT $$ #[u1v1]
    in
      [ MAIN |: H >> C.`> EQ $$ #[u1, u2, atm]
      , MAIN |: H >> C.`> EQ $$ #[v1, v2, atm]
      , MAIN |: H @@ (z, u1v1) >> C.`> EQ $$ #[s1, s2, T]
      , MAIN |: H @@ (z, u1v1') >> C.`> EQ $$ #[t1, t2, T]
      ] BY (fn [D,E,F,G] => D.`> TEST_ATOM_EQ $$ #[D,E,z \\ F, z \\ G]
             | _ => raise Refine)
    end

  fun TestAtomReduceLeft (_ |: H >> P) =
    let
      val #[test, t2, T] = P ^! EQ
      val #[u,v,s,t] = test ^! TEST_ATOM
    in
      [ MAIN |: H >> C.`> EQ $$ #[s, t2, T]
      , AUX |: H >> C.`> EQ $$ #[u, v, C.`> ATOM $$ #[]]
      ] BY mkEvidence TEST_ATOM_REDUCE_LEFT
    end

  fun TestAtomReduceRight (_ |: H >> P) =
    let
      val #[test, t2, T] = P ^! EQ
      val #[u,v,s,t] = test ^! TEST_ATOM
    in
      [ MAIN |: H >> C.`> EQ $$ #[t, t2, T]
      , AUX |: H >> C.`> NOT $$ #[C.`> EQ $$ #[u, v, C.`> ATOM $$ #[]]]
      ] BY mkEvidence TEST_ATOM_REDUCE_RIGHT
    end

   fun MatchTokenEq (_ |: H >> P) =
     let
       val #[match1, match2, C] = P ^! EQ
       val (MATCH_TOKEN toks1, subterms1) = asApp match1
       val (MATCH_TOKEN toks2, subterms2) = asApp match2
       val target1 = Vector.sub (subterms1, 0)
       val target2 = Vector.sub (subterms2, 0)
       fun branches (toks, subterms)=
         Vector.foldri
           (fn (i, tok, dict) =>
             StringListDict.insert dict tok (Vector.sub (subterms, i + 1)))
           StringListDict.empty
           toks

       fun subdomain (keys, dict) = Vector.all (StringListDict.member dict) keys
       val branches1 = branches (toks1, subterms1)
       val branches2 = branches (toks2, subterms2)
       val catchAll1 = Vector.sub (subterms1, Vector.length subterms1 - 1)
       val catchAll2 = Vector.sub (subterms2, Vector.length subterms2 - 1)

       val true =
         subdomain (toks1, branches2)
           andalso subdomain (toks2, branches1)

       val x = Context.fresh (H, Variable.named "x")
       val y = Context.fresh (H, Variable.named "y")

       fun tokToGoal tok =
         let
           val X = C.`> CEQUAL $$ #[target1, C.`> (TOKEN tok) $$ #[]]
           val Y = C.`> CEQUAL $$ #[target2, C.`> (TOKEN tok) $$ #[]]
           val H' = H @@ (x, X) @@ (y, Y)
         in
           MAIN |: H' >> C.`> EQ $$ #[StringListDict.lookup branches1 tok, StringListDict.lookup branches2 tok, C]
         end

       val positiveGoals =
         List.tabulate
           (Vector.length toks1,
            fn i => tokToGoal (Vector.sub (toks1, i)))

       val catchAllGoal =
         let
           val X = C.`> CEQUAL $$ #[match1, catchAll1]
           val Y = C.`> CEQUAL $$ #[match2, catchAll2]
           val H' = H @@ (x, X) @@ (y, Y)
         in
           MAIN |: H' >> C.`> EQ $$ #[catchAll1, catchAll2, C]
         end

       val subgoals =
         (MAIN |: H >> C.`> EQ $$ #[target1, target2, C.`> ATOM $$ #[]])
           :: positiveGoals
            @ [catchAllGoal]
     in
       subgoals BY (fn Ds =>
         D.`> (MATCH_TOKEN_EQ toks1) $$
           Vector.tabulate
             (List.length Ds, fn i =>
                if i = 0 then
                  List.nth (Ds, i)
                else
                  x \\ (y \\ List.nth (Ds, i))))
     end

    structure LevelSolver = LevelSolver (SyntaxWithUniverses (Syntax))
    structure SequentLevelSolver = SequentLevelSolver
      (structure Solver = LevelSolver
       structure Abt = Syntax
       structure Sequent = Sequent)

    local
      open Conversionals
      infix CTHEN

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
                val conv =
                  LevelSolver.subst (LevelSolver.Level.yank k)
                    o CDEEP (convOperator theta world)
              in
                acc CTHEN conv
              end) CID thetas

        in
          [ lbl |: Context.map conv H >> conv P
          ] BY (fn [D] => D
                 | _ => raise Refine)
        end
    end

      fun EqSym (_ |: H >> P) =
        let
          val #[M,N,A] = P ^! EQ
        in
          [ MAIN |: H >> C.`> EQ $$ #[N,M,A]
          ] BY mkEvidence EQ_SYM
        end

      fun EqSubst (eq, xC, ok) (_ |: H >> P) =
        let
          val #[M,N,A] = Context.rebind H eq ^! EQ
          val xC = Context.rebind H xC

          val fvs = List.map #1 (Context.listItems H)
          val meta = Meta.convertFree fvs (xC // M)
          val solution = Unify.unify (Meta.convertFree fvs (xC // M), Meta.convert P)
          val xC = applySolution solution (Meta.convertFree fvs xC)

          val (H', x, C) = ctxUnbind (H, A, xC)
          val k = case ok of SOME k => k | NONE => inferLevel (H', C)
        in
          [ AUX |: H >> eq
          , MAIN |: H >> xC // N
          , AUX |: H' >> C.`> MEM $$ #[C, C.`> (UNIV k) $$ #[]]
          ] BY (fn [D,E,F] => D.`> EQ_SUBST $$ #[D, E, x \\ F]
                 | _ => raise Refine)
      end

    local
      open CttCalculusView
      datatype ForallType = ForallIsect | ForallFun
      structure Tacticals = Tacticals (Lcf)
      open Tacticals
      infix THEN THENL
    in
      fun stripForalls (H, P) =
        case project P of
             ISECT $ #[A, xB] =>
               let
                 val (H', x, B) = ctxUnbind (H, A, xB)
                 val (xs, Q) = stripForalls (H', B)
               in
                 (xs @ [(ForallIsect, x)], Q)
               end
           | FUN $ #[A, xB] =>
               let
                 val (H', x, B) = ctxUnbind (H, A, xB)
                 val (xs, Q) = stripForalls (H', B)
               in
                 (xs @ [(ForallFun, x)], Q)
               end
           | _ => ([], P)

      fun BHyp hyp (goal as _ |: (sequent as H >> P)) =
        let
          val target = eliminationTarget hyp sequent

          val (variables, Q) = stripForalls (H, Context.lookup H target)
          val fvs = List.map #1 (Context.listItems H)
          val solution = Unify.unify (Meta.convertFree fvs Q, Meta.convertFree fvs P)

          val instantiations = List.map (fn (ty, v) => (ty, Unify.Solution.lookup solution v)) variables

          val targetRef = ref target
          fun go [] = ID
            | go ((ty, e) :: es) = fn goal' as _ |: H' >> _ =>
              let
                val currentTarget = Context.rebindName H' (! targetRef)
                val nextTarget = Variable.prime currentTarget
                val _ = targetRef := nextTarget
                val instantiation = Meta.unconvert (fn _ => raise Refine) e
                val eqName = Context.fresh (H', Variable.named "_")
                val names = (nextTarget, eqName)
                val hyp = HypSyn.NAME currentTarget
                val elim =
                  case ty of
                       ForallIsect => IsectElim
                     | ForallFun => FunElim
                val tac =
                  elim (hyp, instantiation, SOME names)
                    THEN Thin hyp
              in
                (tac THENL [ID, go es]) goal'
              end
        in
          go (rev instantiations) goal
        end
    end

    local
      structure Tacticals = Tacticals (Lcf)
      open Tacticals
      infix THEN THENL
    in
      fun HypEqSubst (dir, hyp, xC, ok) (goal as _ |: H >> P) =
        let
          val z = eliminationTarget hyp (H >> P)
          val X = Context.lookup H z
        in
          case dir of
               Dir.RIGHT => (EqSubst (X, xC, ok) THENL [Hypothesis_ z, ID, ID]) goal
             | Dir.LEFT =>
                 let
                   val #[M,N,A] = X ^! EQ
                 in
                   (EqSubst (C.`> EQ $$ #[N,M,A], xC, ok)
                     THENL [EqSym THEN Hypothesis_ z, ID, ID]) goal
                 end
        end

      fun CEqEq (_ |: H >> P) =
        let
          val #[M, N, U] = P ^! EQ
          val (UNIV _, _) = asApp U
          val #[L, R] = M ^! CEQUAL
          val #[L', R'] = N ^! CEQUAL
        in
          [ MAIN |: H >> C.`> CEQUAL $$ #[L, L']
          , MAIN |: H >> C.`> CEQUAL $$ #[R, R']
          ] BY (fn [D, E] => D.`> CEQUAL_EQ $$ #[D, E]
                 | _ => raise Refine)
        end

      fun CEqMemEq (_ |: H >> P) =
        let
          val #[M, N, E] = P ^! EQ
          val #[] = M ^! AX
          val #[] = N ^! AX
          val #[_, _] = E ^! CEQUAL
        in
          [ MAIN |: H >> E
          ] BY mkEvidence CEQUAL_MEMBER_EQ
        end

      fun ApproxEq (_ |: H >> P) =
        let
          val #[approx1, approx2, univ] = P ^! EQ
          val (UNIV _, _) = asApp univ
          val #[M,N] = approx1 ^! APPROX
          val #[M',N'] = approx2 ^! APPROX
          val base = C.`> BASE $$ #[]
        in
          [ MAIN |: H >> C.`> EQ $$ #[M,M',base]
          , MAIN |: H >> C.`> EQ $$ #[N,N',base]
          ] BY mkEvidence APPROX_EQ
        end

      fun ApproxMemEq (_ |: H >> P) =
        let
          val #[M, N, E] = P ^! EQ
          val #[] = M ^! AX
          val #[] = N ^! AX
          val #[_, _] = E ^! APPROX
        in
          [ MAIN |: H >> E
          ] BY mkEvidence APPROX_MEMBER_EQ
        end

      fun ApproxExtEq (_ |: H >> P) =
        let
          val #[approx1, approx2, univ] = P ^! EQ
          val (UNIV _, _) = asApp univ
          val #[_,_] = approx1 ^! APPROX
          val #[_,_] = approx2 ^! APPROX
          val iff = C.`> IFF $$ #[approx1, approx2]
          val squ = C.`> SQUASH $$ #[iff]
        in
          [ MAIN |: H >> squ
          ] BY mkEvidence APPROX_EXT_EQ
        end

      local
        fun bothStuck M N =
          (Semantics.step M; raise Refine)
          handle Semantics.Stuck _ =>
            (Semantics.step N; raise Refine)
               handle Semantics.Stuck _ => ()
      in
        fun ApproxRefl (_ |: H >> P) =
          let
            val #[M, N] = P ^! APPROX
            val () = (unify M N; ()) handle Refine => bothStuck M N
          in
            [] BY mkEvidence APPROX_REFL
          end
      end

      fun ApproxElim hyp (goal as _ |: (sequent as H >> P)) =
        let
          val z = eliminationTarget hyp sequent
          val _ = Context.lookup H z ^! APPROX
          val ax = C.`> AX $$ #[]
          val H' = ctxSubst H ax z
          val P' = subst ax z P
        in
          [ MAIN |: H' >> P'
          ] BY (fn [D] => D.`> APPROX_ELIM $$ #[`` z, D]
                 | _ => raise Refine)
        end

      fun CEqSym (_ |: H >> P) =
        let
          val #[M, N] = P ^! CEQUAL
        in
          [ MAIN |: H >> C.`> CEQUAL $$ #[N, M]
          ] BY (fn [D] => D.`> CEQUAL_SYM $$ #[D]
                 | _ => raise Refine)
        end

      fun CEqStep (_ |: H >> P) =
        let
          val #[M, N] = P ^! CEQUAL
          val M' =
              case Semantics.step M handle Semantics.Stuck _ => raise Refine of
                  Semantics.STEP M' => M'
                | Semantics.CANON => raise Refine
                | Semantics.NEUTRAL => raise Refine
        in
          [ MAIN |: H >> C.`> CEQUAL $$ #[M', N]
          ] BY (fn [D] => D.`> CEQUAL_STEP $$ #[D]
                 | _ => raise Refine)
        end

      fun CEqSubst (eq, xC) (_ |: H >> P) =
        let
          val eq = Context.rebind H eq
          val #[M, N] = eq ^! CEQUAL

          val fvs = List.map #1 (Context.listItems H)
          val meta = Meta.convertFree fvs (xC // M)
          val solution = Unify.unify (Meta.convertFree fvs (xC // M), Meta.convert P)
          val xC = applySolution solution (Meta.convertFree fvs xC)

          val _ = unify P (xC // M)
        in
          [ AUX |: H >> eq
          , MAIN |: H >> xC // N
          ] BY (fn [D, E] => D.`> CEQUAL_SUBST $$ #[D, E]
                 | _ => raise Refine)
        end

      fun HypCEqSubst (dir, hyp, xC) (goal as _ |: H >> P) =
        let
          val z = eliminationTarget hyp (H >> P)
          val X = Context.lookup H z
        in
          case dir of
              Dir.RIGHT =>
              (CEqSubst (X, xC) THENL [Hypothesis_ z, ID]) goal
            | Dir.LEFT =>
              let
                val #[M,N] = X ^! CEQUAL
              in
                (CEqSubst (C.`> CEQUAL $$ #[N,M], xC)
                          THENL [CEqSym THEN Hypothesis_ z, ID]) goal
              end
        end

      fun CEqApprox (_ |: H >> P) =
        let
          val #[M, N] = P ^! CEQUAL
        in
          [ MAIN |: H >> C.`> APPROX $$ #[M, N]
          , MAIN |: H >> C.`> APPROX $$ #[N, M]
          ] BY mkEvidence CEQUAL_APPROX
        end

      fun AssumeHasValue (onames, ok) (_ |: H >> P) =
        let
          val #[M,N] = P ^! APPROX
          val y =
            case onames of
                 SOME names => names
               | NONE => Context.fresh (H, Variable.named "y")
          val hv = C.`> HASVALUE $$ #[M]
          val k = case ok of SOME k => k | NONE => inferLevel (H, hv)
          val uni = C.`> (UNIV k) $$ #[]
          val mem = C.`> MEM $$ #[hv, uni]
        in
          [ MAIN |: H @@ (y, hv) >> P
          , AUX |: H >> mem
          ] BY (fn [A,B] => D.`> ASSUME_HAS_VALUE $$ #[y \\ A,B]
                 | _ => raise Refine)
        end

      fun BottomDiverges hyp (_ |: H >> P) =
        let
          val x = eliminationTarget hyp (H >> P)
          val h = Context.lookup H x
          val #[M] = h ^! HASVALUE
          val #[] = M ^! BOT
        in
          [] BY (fn _ => D.`> BOTTOM_DIVERGES $$ #[``x])
        end

      local
        (* Create a new subgoal by walking along the pairs
         * of terms and unbind each term together. As we go
         * we add the new variables to the context as we go
         * and keep track of all the variables we bind.
         *
         * In the end you get a new goal and a list of variables in the
         * order that they were created.
         *)
        fun newSubGoal H vs (t1, t2) =
          case (out t1, out t2) of
              (x \ t1', y \ t2') =>
              newSubGoal (H @@ (x, C.`> BASE $$ #[]))
                         (x :: vs)
                         (t1', subst (``x) y t2')
            | (_, _) =>
              (List.rev vs, MAIN |: H >> C.`> CEQUAL $$ #[t1, t2])

        fun toList v = Vector.foldr op:: nil v

        (* Each derivation needs to bind the variables from the
         * context so all we do is take a vector of lists of variables
         * and a vector of terms and bind all the variables in one list
         * in the corresponding term.
         *)
        fun bindVars vars terms =
          let
            fun go [] t = t
              | go (v :: vs) t = go vs (v \\ t)
          in
            Vector.tabulate (Vector.length terms,
                             fn i => go (Vector.sub (vars, i))
                                        (Vector.sub (terms, i)))
          end

      in
        fun CEqStruct (_ |: H >> P) =
          let
            val #[M, N] = P ^! CEQUAL
            val (oper, subterms) = asApp M
            val subterms' = N ^! oper
            val pairs =
                Vector.tabulate (Vector.length subterms,
                                 (fn i => (Vector.sub(subterms, i),
                                           Vector.sub(subterms', i))))
            val (boundVars, subgoals) =
                ListPair.unzip (toList (Vector.map (newSubGoal H []) pairs))
            val boundVars = Vector.fromList boundVars
          in
            subgoals BY (fn Ds =>
                            D.`> (CEQUAL_STRUCT (Vector.map List.length boundVars))
                              $$ bindVars boundVars (Vector.fromList Ds)
                            handle _ => raise Refine)
          end
        end
    end
  end

  structure Conversions =
  struct
    open Conv

    val Step : conv = fn M =>
      case Semantics.step M of
           Semantics.STEP M' => M'
         | _ => raise Conv
  end
end

structure Refiner = Refiner
  (structure Lcf = Lcf
   structure Syntax = Syntax
   structure Conv = Conv
   structure Semantics = Semantics
   structure Sequent = Sequent
   structure Development = Development
   structure Builtins = Builtins)
