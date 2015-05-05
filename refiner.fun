functor Refiner
  (structure Syn : ABTUTIL where Operator = Lang
   val print_mode : PrintMode.t) :>
sig

  structure Evidence : ABTUTIL
  exception MalformedEvidence of Evidence.t
  val extract : Evidence.t -> Syn.t

  structure Context : CONTEXT
    where type name = Syn.Variable.t

  type context = Syn.t Context.context
  datatype sequent = >> of context * Syn.t

  include REFINER_TYPES
    where type goal = sequent
    and type evidence = Evidence.t

  val print_goal : goal -> string

  structure CoreTactics : CORE_TACTICS
    where type tactic = tactic

  structure InferenceRules :
  sig
    val VoidEq : tactic
    val VoidElim : tactic

    val UnitEq : tactic
    val UnitIntro : tactic
    val UnitElim : Context.name -> tactic
    val AxEq : tactic

    val ProdEq : Context.name -> tactic
    val ProdIntro : Syn.t -> tactic
    val ProdElim : Context.name * Context.name * Context.name -> tactic
    val PairEq : Context.name -> tactic

    val FunEq : Context.name -> tactic
    val FunIntro : Context.name -> tactic
    val LamEq : Context.name -> tactic

    val MemIntro : tactic
    val EqIntro : tactic
    val Witness : Syn.t -> tactic

    val Assumption : tactic
    val Hypothesis : Context.name -> tactic
    val HypEq : tactic
  end

  structure DerivedTactics :
  sig
    val Auto : tactic
  end
end =
struct
  structure Context = Context(Syn.Variable)
  type context = Syn.t Context.context

  datatype sequent = >> of context * Syn.t
  infix 3 >>

  fun ctx_subst (G : context) (m : Syn.t) (x : Context.name) =
    Context.map (Syn.subst m x) G

  structure EOp =
  struct
    datatype t
      = VOID_EQ
      | UNIT_INTRO | UNIT_EQ | UNIT_ELIM of Context.name
      | PROD_INTRO of Syn.t | PROD_EQ | PROD_ELIM of Context.name
      | FUN_INTRO | FUN_EQ | LAM_EQ
      | AX_EQ
      | PAIR_EQ
      | MEM_INTRO
      | EQ_INTRO
      | WITNESS of Syn.t
      | HYP_EQ
      | VOID_ELIM

    fun eq UNIT_INTRO UNIT_INTRO = true
      | eq VOID_EQ VOID_EQ = true
      | eq UNIT_EQ UNIT_EQ = true
      | eq (UNIT_ELIM x) (UNIT_ELIM y) = Syn.Variable.eq x y
      | eq (PROD_INTRO x) (PROD_INTRO y) = Syn.eq (x, y)
      | eq PROD_EQ PROD_EQ = true
      | eq PAIR_EQ PAIR_EQ = true
      | eq (PROD_ELIM z) (PROD_ELIM z') = Syn.Variable.eq z z'
      | eq FUN_INTRO FUN_INTRO = true
      | eq FUN_EQ FUN_EQ = true
      | eq AX_EQ AX_EQ = true
      | eq LAM_EQ LAM_EQ = true
      | eq MEM_INTRO MEM_INTRO = true
      | eq EQ_INTRO EQ_INTRO = true
      | eq (WITNESS m) (WITNESS n) = Syn.eq (m, n)
      | eq HYP_EQ HYP_EQ = true
      | eq VOID_ELIM VOID_ELIM = true
      | eq _ _ = false

    fun arity UNIT_INTRO = #[]
      | arity VOID_EQ = #[]
      | arity UNIT_EQ = #[]
      | arity (UNIT_ELIM _) = #[0]
      | arity (PROD_INTRO _) = #[0,0]
      | arity (PROD_ELIM _) = #[2]
      | arity PROD_EQ = #[0,1]
      | arity FUN_INTRO = #[1,0]
      | arity FUN_EQ = #[0,1]
      | arity AX_EQ = #[]
      | arity PAIR_EQ = #[0,0,1]
      | arity LAM_EQ = #[1,0]
      | arity MEM_INTRO = #[0]
      | arity EQ_INTRO = #[0]
      | arity (WITNESS _) = #[0]
      | arity HYP_EQ = #[0]
      | arity VOID_ELIM = #[0]

    fun to_string UNIT_INTRO = "unit-I"
      | to_string UNIT_EQ = "unit="
      | to_string (UNIT_ELIM x) = "unit-E{" ^ Syn.Variable.to_string print_mode x ^ "}"
      | to_string VOID_EQ = "void="
      | to_string (PROD_INTRO w) = "prod-I{" ^ Syn.to_string print_mode w ^ "}"
      | to_string (PROD_ELIM x) = "prod-E{" ^ Syn.Variable.to_string print_mode x ^ "}"
      | to_string PROD_EQ = "prod="
      | to_string FUN_INTRO = "fun-I"
      | to_string FUN_EQ = "fun="
      | to_string AX_EQ = "ax="
      | to_string PAIR_EQ = "pair="
      | to_string LAM_EQ = "lam="
      | to_string MEM_INTRO = "∈*-I"
      | to_string EQ_INTRO = "=*-I"
      | to_string (WITNESS m) = "witness{" ^ Syn.to_string print_mode m ^ "}"
      | to_string HYP_EQ = "hyp-∈"
      | to_string VOID_ELIM = "void-E"
  end

  structure Evidence =
    AbtUtil
      (Abt
        (structure Operator = EOp
         and Variable = Syn.Variable))

  structure E = Evidence

  structure RefinerTypes : REFINER_TYPES =
  struct
    type goal = sequent
    type evidence = E.t
    type validation = evidence list -> evidence
    type tactic = goal -> (goal list * validation)
  end

  open RefinerTypes

  exception MalformedEvidence of E.t

  local
    open E EOp Lang
    infix $ \
    exception Hole
  in
    fun extract (ev : E.t) : Syn.t =
      case out ev of
           VOID_EQ $ _ => Syn.$$ (AX, #[])
         | VOID_ELIM $ _ => Syn.$$ (AX, #[])

         | UNIT_EQ $ _ => Syn.$$ (AX, #[])
         | UNIT_INTRO $ #[] => Syn.$$ (AX, #[])
         | UNIT_ELIM x $ #[E] => Syn.$$ (MATCH_UNIT, #[Syn.`` x, extract E])
         | AX_EQ $ _ => Syn.$$ (AX, #[])

         | PROD_EQ $ _ => Syn.$$ (AX, #[])
         | PROD_INTRO w $ #[D,E] => Syn.$$ (PAIR, #[w, extract E])
         | PROD_ELIM z $ #[stD] => Syn.$$ (SPREAD, #[Syn.`` z, extract stD])
         | PAIR_EQ $ _ => Syn.$$ (AX, #[])

         | FUN_EQ $ _ => Syn.$$ (AX, #[])
         | FUN_INTRO $ #[xE, _] => Syn.$$ (LAM, #[extract xE])
         | LAM_EQ $ _ => Syn.$$ (AX, #[])

         | MEM_INTRO $ _ => Syn.$$ (AX, #[])
         | HYP_EQ $ _ => Syn.$$ (AX, #[])
         | WITNESS m $ _ => m
         | ` x => Syn.`` x
         | x \ E => Syn.\\ (x, extract E)
         | _ => raise Fail (E.to_string print_mode ev)
  end


  open Lang
  open Syn EOp
  infix $
  infix 8 $$

  val %$$ = Evidence.$$
  infix %$$

  val %\\ = Evidence.\\
  infix %\\

  val %`` = Evidence.``

  structure Whnf = Whnf(Syn)

  structure CoreTactics = CoreTactics(RefinerTypes)

  fun print_goal (G >> P) =
    let
      val ctx = Context.to_string (print_mode, Syn.to_string) G
      val prop = Syn.to_string print_mode P
    in
      ctx ^ " >> " ^ prop
    end


  structure InferenceRules =
  struct
    exception Refine

    fun named name (tac : tactic) : tactic = fn (goal : goal) =>
      let
        fun fail () = raise Fail (name ^ "| " ^ print_goal goal)
        val (subgoals, validation) = tac goal handle Refine => fail ()
      in
        (subgoals, fn Ds => validation Ds handle Refine => fail ())
      end

    fun mk_evidence operator = fn Ds => operator %$$ Vector.fromList Ds

    fun BY (Ds, V) = (Ds, V)
    infix BY

    fun // (xM, N) = subst1 xM N
    infix 7 //

    fun @@ (G, (x,A)) = Context.insert G x A
    infix 8 @@

    val UnitIntro : tactic =
      named "UnitIntro" (fn (G >> P) =>
        case out P of
             UNIT $ _ => [] BY mk_evidence UNIT_INTRO
           | _ => raise Refine)

    fun UnitElim x : tactic =
      named "UnitElim" (fn (G >> P) =>
        case Context.lookup G x of
             SOME unit => (case out unit of
                 UNIT $ #[] =>
                   let
                     val ax = AX $$ #[]
                     val G' = ctx_subst G ax x
                     val P' = subst ax x P
                   in
                     [ G' >> P'
                     ] BY mk_evidence (UNIT_ELIM x)
                   end
               | _ => raise Refine)
           | NONE => raise Refine)

    val UnitEq : tactic =
      named "UnitEq" (fn (G >> P) =>
        case out P of
             CAN_MEM $ #[unit, unit', univ] =>
               (case (out unit, out unit', out univ) of
                    (UNIT $ _, UNIT $ _, UNIV $ _) =>
                      [] BY mk_evidence UNIT_EQ
                  | _ => raise Refine)
           | _ => raise Refine)

    val VoidEq : tactic =
      named "VoidEq" (fn (G >> P) =>
        case out P of
             CAN_MEM $ #[void, void', univ] =>
               (case (out void, out void', out univ) of
                    (VOID $ _, VOID $ _, UNIV $ _) =>
                      [] BY mk_evidence VOID_EQ
                  | _ => raise Refine)
           | _ => raise Refine)

    val VoidElim : tactic =
      named "VoidEq" (fn (G >> P) =>
        [ G >> VOID $$ #[]
        ] BY mk_evidence VOID_ELIM)

    val AxEq : tactic =
      named "AxEq" (fn (G >> P) =>
        case out P of
             CAN_EQ $ #[ax, ax', unit] =>
               (case (out ax, out ax', out unit) of
                    (AX $ #[], AX $ #[], UNIT $ #[]) =>
                      [] BY mk_evidence AX_EQ
                  | _ => raise Refine)
           | _ => raise Refine)

    fun FunEq z : tactic =
      named "FunEq" (fn (G >> P) =>
        case out P of
             CAN_EQ $ #[fun1, fun2, univ] =>
               (case (out fun1, out fun1, out univ) of
                    (FUN $ #[A,xB], FUN $ #[A',yB'], UNIV $ #[]) =>
                      [ G >> EQ $$ #[A,A',univ]
                      , G @@ (z,A) >> EQ $$ #[xB // ``z, yB' // `` z, univ]
                      ] BY (fn [D, E] => FUN_EQ %$$ #[D, z %\\ E]
                             | _ => raise Refine)
                  | _ => raise Refine)
           | _ => raise Refine)

    fun FunIntro z : tactic =
      named "FunIntro" (fn (G >> P) =>
        case out P of
             FUN $ #[P1, xP2] =>
               [ G @@ (z,P1) >> xP2 // `` z
               , G >> MEM $$ #[P1, UNIV $$ #[]]
               ] BY (fn [D,E] => FUN_INTRO %$$ #[z %\\ D, E]
                      | _ => raise Refine)
           | _ => raise Refine)

    fun LamEq z : tactic =
      named "LamEq" (fn (G >> P) =>
        case out P of
             CAN_EQ $ #[lam, lam', func] =>
               (case (out lam, out lam', out func) of
                     (LAM $ #[aE], LAM $ #[bE'], FUN $ #[A,cB]) =>
                       [ G @@ (z,A) >> EQ $$ #[aE // ``z, bE' // ``z, cB // ``z]
                       , G >> MEM $$ #[A, UNIV $$ #[]]
                       ] BY (fn [D, E] => LAM_EQ %$$ #[z %\\ D, E]
                               | _ => raise Refine)
                   | _ => raise Refine)
           | _ => raise Refine)

    val MemIntro : tactic =
      named "MemIntro" (fn (G >> P) =>
      case out P of
           MEM $ #[M, A] =>
             [ G >> EQ $$ #[M, M, A]
             ] BY mk_evidence MEM_INTRO
         | _ => raise Refine)

    val EqIntro : tactic =
      named "EqIntro" (fn (G >> P) =>
        case out P of
             EQ $ #[M, N, A] =>
               let
                 val M0 = Whnf.whnf M
                 val N0 = Whnf.whnf N
                 val A0 = Whnf.whnf A
               in
                 [ G >> CAN_EQ $$ #[M0, N0, A0]
                 ] BY mk_evidence EQ_INTRO
               end
           | _ => raise Refine)

    fun Witness M : tactic =
      named "Witness" (fn (G >> P) =>
        [ G >> MEM $$ #[M, P]
        ] BY mk_evidence (WITNESS M))

    val HypEq : tactic =
      named "HypEq" (fn (G >> P) =>
        case out P of
             EQ $ #[M,M',A] =>
             (case (Syn.eq (M, M'), out M) of
                   (true, ` x) =>
                     (case Context.lookup G x of
                           SOME Q =>
                             if Syn.eq (A, Q)
                             then ([], fn _ => HYP_EQ %$$ #[%`` x])
                             else raise Refine
                         | NONE => raise Refine)
                 | _ => raise Refine)
           | _ => raise Refine)

    fun ProdEq z : tactic =
      named "ProdEq" (fn (G >> P) =>
        case out P of
             CAN_EQ $ #[prod1, prod2, univ] =>
               (case (out prod1, out prod2, out univ) of
                    (PROD $ #[A,xB], PROD $ #[A',yB'], UNIV $ #[]) =>
                      [ G >> EQ $$ #[A,A',univ]
                      , G @@ (z,A) >> EQ $$ #[xB // ``z, yB' // ``z, univ]
                      ] BY (fn [D, E] => PROD_EQ %$$ #[D, z %\\ E]
                             | _ => raise Refine)
                  | _ => raise Refine)
           | _ => raise Refine)

    fun ProdIntro w : tactic =
      named "ProdIntro" (fn (G >> P) =>
        case out P of
             PROD $ #[P1, xP2] =>
               [ G >> MEM $$ #[ w, P1]
               , G >> xP2 // w
               ] BY mk_evidence (PROD_INTRO w)
           | _ => raise Refine)

    fun ProdElim (z, s, t) : tactic =
      named "ProdElim" (fn (G >> P) =>
        case Context.lookup G z of
             SOME Q => (case out Q of
                 PROD $ #[ S, xT ] =>
                   let
                     val st = PAIR $$ #[``s, ``t]
                   in
                     [ ctx_subst G st z >> subst st z P
                     ] BY (fn [D] => PROD_ELIM z %$$ #[s %\\ (t %\\ D)]
                            | _ => raise Refine)
                   end
               | _ => raise Refine)
           | NONE => raise Refine
      )

    fun PairEq z : tactic =
      named "PairEq" (fn (G >> P) =>
        case out P of
             CAN_EQ $ #[pair, pair', prod] =>
               (case (out pair, out pair', out prod) of
                     (PAIR $ #[M,N], PAIR $ #[M', N'], PROD $ #[A,xB]) =>
                       [ G >> EQ $$ #[M, M', A]
                       , G >> EQ $$ #[N, N', xB // M]
                       , G @@ (z,A) >> MEM $$ #[xB // `` z, UNIV $$ #[]]
                       ] BY (fn [D,E,F] => PAIR_EQ %$$ #[D, E, z %\\ F]
                              | _ => raise Refine)
                   | _ => raise Refine)
           | _ => raise Refine)

    fun Hypothesis x : tactic =
      named "Hypothesis" (fn (G >> P) =>
        case Context.lookup G x of
              SOME P' =>
                if Syn.eq (P, P')
                then [] BY (fn _ => %`` x)
                else raise Refine
            | NONE => raise Refine)

    val Assumption : tactic =
      named "Assumption" (fn (G >> P) =>
        case Context.search G (fn x => Syn.eq (P, x)) of
             SOME (x, _) => [] BY (fn _ => %`` x)
           | NONE => raise Refine)
  end

  structure DerivedTactics =
  struct
    open CoreTactics InferenceRules
    infix ORELSE ORELSE_LAZY THEN

    local
      val CanEqAuto = AxEq ORELSE_LAZY (fn () => PairEq (Variable.new ())) ORELSE_LAZY (fn () => LamEq (Variable.new ())) ORELSE UnitEq ORELSE_LAZY (fn () => ProdEq (Variable.new())) ORELSE VoidEq
      val EqAuto = (EqIntro THEN CanEqAuto) ORELSE HypEq
      val intro_rules =
        MemIntro ORELSE
          EqAuto ORELSE
            Assumption ORELSE_LAZY
              (fn () => FunIntro (Variable.new ())) ORELSE
                UnitIntro
    in
      val Auto = REPEAT intro_rules
    end
  end
end

