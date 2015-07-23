functor UnifySequent(Sequent : SEQUENT) :>
  UNIFY_SEQUENT where Sequent = Sequent =
struct
  exception Mismatch

  structure Sequent = Sequent
  structure Rebind  = Rebind(Sequent.Context.Syntax)

  open Sequent
  infix >>

  type input =
       {hyps : term list,
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

  fun convertInCtx H M =
    let
      open MetaAbt
      val ctxVars = List.map #1 (Context.listItems H)
      val M = Rebind.rebind ctxVars M
      val freeVars =
          diff Context.Syntax.Variable.eq
               (Context.Syntax.freeVariables M)
               ctxVars
    in
      List.foldl (fn (v, M') => subst ($$ (MetaOperator.META v, #[])) v M')
                 (convert M)
                 freeVars
    end

  fun rebindPat {goal, hyps} =
    let
      open Context.Syntax
      val free = freeVariables goal
      val (_, hyps) =
        List.foldl (fn (h, (free, hyps)) =>
                       let
                         val h = Rebind.rebind free h
                       in
                         (freeVariables h @ free, h :: hyps)
                       end)
                   (free, [])
                   hyps
    in
      {goal = goal, hyps = hyps}
    end

  fun applySol sol e =
    List.foldl
      (fn ((v, e'), e) =>
          MetaAbt.substOperator (fn #[] => e') (MetaOperator.META v) e)
      e
      sol

  (* Merge a pair of solutions where no variable in the first solution
   * appears in the second solution (either as a variable or in a term).
   *)
  fun mergeSol (sol1, sol2) =
    let
      fun eq ((v, _), (v', _)) = Context.Syntax.Variable.eq (v, v')
      val sol1' = List.map (fn (v, e) => (v, applySol sol2 e)) sol1
    in
      sol2 @ diff eq sol1' sol2
    end

  (* Given a a list of terms and set of hypotheses and the current
   * solution, attempt to match the terms against some subset of hypotheses
   * and return
   *   1. Those hypotheses
   *   2. The new solution
   *)
  fun matchCxt sol [] _ = SOME ([], sol)
    | matchCxt sol (t :: ts) hs =
      let
          val len = List.length hs
          fun go 0 = NONE
            | go n =
              let
                val ((name, h), hs) = extract (len - n) hs
                val sol = mergeSol (sol, Unify.unify (applySol sol t, h))
              in
                case matchCxt sol ts hs of
                    SOME (names, sol) => (SOME (name :: names, sol))
                  | NONE => go (n - 1)
              end
              handle Unify.Mismatch _ => go (n - 1)
      in
        go len
      end

  fun unify (pat, H >> P) =
    let
      val {hyps, goal} = rebindPat pat
      val goal = convertInCtx H goal
      val hyps = List.map (convertInCtx H) hyps
      val sol = Unify.unify (goal, convert P)
                  handle Unify.Mismatch _ => raise Mismatch

      fun go [] = raise Mismatch
        | go (hs :: subsets) =
          case matchCxt sol hyps hs of
              SOME (names, finalSol) =>
              {matched = names,
               subst = List.map (fn (v, e) => (v, unconvert e)) finalSol}
            | NONE => go subsets
      val subsets = subset (List.map (fn (n, v, t) => (n, convert t))
                           (Context.listItems H))
                           (List.length hyps)
    in
      go subsets
    end
end
