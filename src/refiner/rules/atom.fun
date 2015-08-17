functor AtomRules(Utils : RULES_UTIL) : ATOM_RULES =
struct
  open Utils
  open Goal Sequent Syntax CttCalculus Derivation

  infix $ \ BY ^!
  infix 3 >>
  infix 2 |:
  infix 8 $$ // @@
  infixr 8 \\

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
end
