functor UnifySequent(Sequent : SEQUENT) :>
  UNIFY_SEQUENT where Sequent = Sequent =
struct
  exception Mismatch

  structure Sequent = Sequent
  structure Rebind  = Rebind(Sequent.Context.Syntax)

  open Sequent
  infix >>

  type input =
       {hyps : (name * term) list,
        goal : term}
  type output =
       {matched : name list,
        subst : (Context.Syntax.Variable.t * term) list}

  (* Unification stuff *)
  structure Meta = MetaAbt(Context.Syntax)
  open Meta

  structure MetaAbt = AbtUtil(Meta)
  structure Unify = AbtUnifyOperators
    (structure A = MetaAbt
     structure O = MetaOperator)
  structure Sol = Unify.Solution

  (* List utilities we seem to need *)

  (* Remove one list from another *)
  fun diff eq xs ys =
    List.filter (fn x => not (List.exists (fn y => eq (x, y)) ys)) xs

  (* OK this is just awful. But it's the simplest working idea I have. *)
  fun subset H 0 = [[]]
    | subset [] _ = []
    | subset (x :: xs) n =
      subset xs n @ List.map (fn xs => x :: xs) (subset xs (n - 1))

  (* Remove the nth element of a list and return it and the list
   * with it removed
   *)
  fun extract _ [] = raise Mismatch
    | extract 0 (x :: xs) = (x, xs)
    | extract n (x :: xs) =
      let
        val (y, ys) = extract (n - 1) xs
      in
        (y, x :: ys)
      end

  fun convertInCtx hypVars H M =
    let
      open MetaAbt
      val ctxVars =
        diff Context.Syntax.Variable.eq
             (List.map #1 (Context.listItems H))
             hypVars
      val M = Rebind.rebindPrefix "'" ctxVars M
      val freeVars =
        diff Context.Syntax.Variable.eq
             (Context.Syntax.freeVariables M)
             ctxVars

      val wildVars = List.filter (fn v => "_" = Variable.toString v) freeVars
      val wild = MetaAbt.into (MetaAbt.$ (MetaOperator.WILD, #[]))
      (* Assert that all free variables are ones we didn't mean to
       * bind to ones in the context already.
       *)
      val () =
        if List.exists (String.isPrefix "'") (List.map Variable.toString freeVars)
        then raise Mismatch
        else ()
      val cM =
        List.foldl (fn (v, M') => subst ($$ (MetaOperator.META v, #[])) v M')
                   (convert M)
                   freeVars
    in
      List.foldl
        (fn (v, t) => substOperator (fn _ => wild) (MetaOperator.META v) t)
        cM
        wildVars
    end

  fun rebindPat {goal, hyps} =
    let
      open Context.Syntax
      val free = freeVariables goal

      val (_, hyps) =
        List.foldl (fn ((name, h), (free, hyps)) =>
                       let
                         (* This uses actual rebind because we're not dealing
                          * with anything in the context, we're ensuring that
                          * within the pattern all identically named variables
                          * are identical so we needn't worry about 's.
                          *)
                         val h = Rebind.rebind free h
                         val free = freeVariables h @ free
                       in
                         (name :: free, (name, h) :: hyps)
                       end)
                   (free, [])
                   hyps
    in
      {goal = goal, hyps = hyps}
    end

  fun applySol sol e =
    Sol.foldl
      (fn (v, e', e) =>
          MetaAbt.substOperator (fn #[] => e') (MetaOperator.META v) e)
      e
      sol

  (* Merge a pair of solutions where no variable in the first solution
   * appears in the second solution (either as a variable or in a term).
   *)
  fun mergeSol (sol1, sol2) =
    let
      val sol1' = Sol.map (applySol sol2) sol1
    in
      Sol.union sol2 sol1' (fn (_, e, _) => e)
    end

  fun add sol (v, e) =
    let
      open MetaOperator
      open MetaAbt
      val e = applySol sol e
      val sol = Sol.map (substOperator (fn _ => e) (META v)) sol
    in
      case Sol.find sol v of
          NONE => Sol.insert sol v e
        | SOME e' =>
          if eq (e, e')
          then sol
          else raise Mismatch
    end

  (* Given a a list of terms and set of hypotheses and the current
   * solution, attempt to match the terms against some subset of hypotheses
   * and return
   *   1. Those hypotheses
   *   2. The new solution
   *)
  fun matchCxt sol [] _ = SOME ([], sol)
    | matchCxt sol ((name, t) :: ts) hs =
      let
          val len = List.length hs
          fun go 0 = NONE
            | go n =
              let
                val ((hname, h), hs) = extract (len - n) hs
                val sol = mergeSol (sol, Unify.unify (applySol sol t, h))
                val sol = add sol (name, MetaAbt.into (MetaAbt.` hname))
              in
                case matchCxt sol ts hs of
                    SOME (names, sol) => (SOME (hname :: names, sol))
                  | NONE => go (n - 1)
              end
              handle Unify.Mismatch _ => go (n - 1)
      in
        go len
      end

  fun unify (pat, H >> P) =
    let
      val {hyps, goal} = rebindPat pat
      val hypVars = List.map #1 hyps
      val goal = convertInCtx hypVars H goal
      val hyps = List.map (fn (n, e) => (n, convertInCtx hypVars H e)) hyps
      val sol = Unify.unify (goal, convert P)
                  handle Unify.Mismatch _ => raise Mismatch

      exception Wildcard
      fun go [] = raise Mismatch
        | go (hs :: subsets) =
          case matchCxt sol hyps hs of
              SOME (names, finalSol) =>
              {matched = names,
               subst = Sol.toList (Sol.map (unconvert (fn _ => raise Wildcard)) finalSol)}
            | NONE => go subsets
      val subsets = subset (List.map (fn (n, v, t) => (n, convert t))
                           (Context.listItems H))
                           (List.length hyps)
    in
      go subsets
    end
end
