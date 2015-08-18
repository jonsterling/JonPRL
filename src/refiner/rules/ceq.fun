functor CEqRules(Utils : RULES_UTIL) : CEQ_RULES =
struct
  open Utils
  open Goal Sequent Syntax CttCalculus Derivation

  infix $ \ BY ^!
  infix 3 >>
  infix 2 |:
  infix 8 $$ // @@
  infixr 8 \\

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

  fun CEqApprox (_ |: H >> P) =
    let
      val #[M, N] = P ^! CEQUAL
    in
      [ MAIN |: H >> C.`> APPROX $$ #[M, N]
      , MAIN |: H >> C.`> APPROX $$ #[N, M]
      ] BY mkEvidence CEQUAL_APPROX
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

  local
    structure Tacticals = Tacticals (Lcf)
    open Tacticals
    infix THEN THENL
  in
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
