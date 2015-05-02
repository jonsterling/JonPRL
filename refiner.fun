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

  include REFINER_TYPES
    where type goal = context * Syn.t
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
    val AxEq : tactic

    val ProdEq : tactic
    val ProdIntro : tactic

    val FunEq : tactic
    val FunIntro : tactic
    val LamEq : tactic

    val MemIntro : tactic
    val EqIntro : tactic
    val Witness : Syn.t -> tactic

    val PairEq : tactic

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
  type goal = context * Syn.t

  structure EOp =
  struct
    datatype t
      = VOID_EQ
      | UNIT_INTRO | UNIT_EQ
      | PROD_INTRO | PROD_EQ
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
      | eq PROD_INTRO PROD_INTRO = true
      | eq PROD_EQ PROD_EQ = true
      | eq FUN_INTRO FUN_INTRO = true
      | eq FUN_EQ FUN_EQ = true
      | eq AX_EQ AX_EQ = true
      | eq PAIR_EQ PAIR_EQ = true
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
      | arity PROD_INTRO = #[0,0]
      | arity PROD_EQ = #[0,0]
      | arity FUN_INTRO = #[1,0]
      | arity FUN_EQ = #[0,1]
      | arity AX_EQ = #[]
      | arity PAIR_EQ = #[0,0]
      | arity LAM_EQ = #[1,0]
      | arity MEM_INTRO = #[0]
      | arity EQ_INTRO = #[0]
      | arity (WITNESS _) = #[0]
      | arity HYP_EQ = #[0]
      | arity VOID_ELIM = #[0]

    fun to_string UNIT_INTRO = "unit-I"
      | to_string UNIT_EQ = "unit="
      | to_string VOID_EQ = "void="
      | to_string PROD_INTRO = "prod-I"
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
    type goal = goal
    type evidence = E.t
    type validation = evidence list -> evidence
    type tactic = goal -> (goal list * validation)
  end

  open RefinerTypes

  exception MalformedEvidence of E.t

  local
    open E EOp Lang
    infix $ \
  in
    fun extract (ev : E.t) : Syn.t =
      case out ev of
           UNIT_INTRO $ #[] => Syn.$$ (AX, #[])
         | PROD_INTRO $ #[D,E] => Syn.$$ (PAIR, #[extract D, extract E])
         | FUN_INTRO $ #[xE, _] => Syn.$$ (LAM, #[extract xE])
         | AX_EQ $ _ => Syn.$$ (AX, #[])
         | PAIR_EQ $ _ => Syn.$$ (AX, #[])
         | LAM_EQ $ _ => Syn.$$ (AX, #[])
         | MEM_INTRO $ _ => Syn.$$ (AX, #[])
         | VOID_ELIM $ _ => Syn.$$ (AX, #[])
         | UNIT_EQ $ _ => Syn.$$ (AX, #[])
         | VOID_EQ $ _ => Syn.$$ (AX, #[])
         | PROD_EQ $ _ => Syn.$$ (AX, #[])
         | FUN_EQ $ _ => Syn.$$ (AX, #[])
         | HYP_EQ $ _ => Syn.$$ (AX, #[])
         | WITNESS m $ _ => m
         | ` x => Syn.`` x
         | x \ E => Syn.\\ (x, extract E)
         | _ => raise Fail (E.to_string print_mode ev)
  end


  open Lang
  open Syn EOp
  infix $
  infix $$

  val %$$ = Evidence.$$
  infix %$$

  val %\\ = Evidence.\\
  infix %\\

  val %`` = Evidence.``

  structure Whnf = Whnf(Syn)

  structure CoreTactics = CoreTactics(RefinerTypes)

  fun print_goal (G, P) =
    let
      val ctx = Context.to_string (print_mode, Syn.to_string) G
      val prop = Syn.to_string print_mode P
    in
      ctx ^ " >> " ^ prop
    end


  structure InferenceRules =
  struct
    exception Refine

    fun named name tac = fn goal =>
      let
        fun fail () = raise Fail (name ^ "| " ^ print_goal goal)
        val (subgoals, validation) = tac goal handle Refine => fail ()
      in
        (subgoals, fn Ds => validation Ds handle Refine => fail ())
      end

    fun mk_evidence operator = fn Ds => operator %$$ Vector.fromList Ds

    val UnitIntro : tactic =
      named "UnitIntro" (fn (G, P) =>
        case out P of
             UNIT $ _ => ([], mk_evidence UNIT_INTRO)
           | _ => raise Refine)

    val UnitEq : tactic =
      named "UnitEq" (fn (G, P) =>
        case out P of
             CAN_MEM $ #[unit, unit', univ] =>
               (case (out unit, out unit', out univ) of
                    (UNIT $ _, UNIT $ _, UNIV $ _) => ([], mk_evidence UNIT_EQ)
                  | _ => raise Refine)
           | _ => raise Refine)

    val VoidEq : tactic =
      named "VoidEq" (fn (G, P) =>
        case out P of
             CAN_MEM $ #[void, void', univ] =>
               (case (out void, out void', out univ) of
                    (VOID $ _, VOID $ _, UNIV $ _) => ([], mk_evidence VOID_EQ)
                  | _ => raise Refine)
           | _ => raise Refine)

    val VoidElim : tactic =
      named "VoidEq" (fn (G, P) =>
        ([(G, VOID $$ #[])], mk_evidence VOID_ELIM))

    val AxEq : tactic =
      named "AxEq" (fn (G, P) =>
        case out P of
             CAN_EQ $ #[ax, ax', unit] =>
               (case (out ax, out ax', out unit) of
                    (AX $ #[], AX $ #[], UNIT $ #[]) =>
                      ([], mk_evidence AX_EQ)
                  | _ => raise Refine)
           | _ => raise Refine)

    val PairEq : tactic =
      named "PairEq" (fn (G, P) =>
        case out P of
             CAN_EQ $ #[pair, pair', prod] =>
               (case (out pair, out pair', out prod) of
                     (PAIR $ #[M,N], PAIR $ #[M', N'], PROD $ #[A,B]) =>
                       ([(G, EQ $$ #[M,M',A]), (G, EQ $$ #[N,N',B])],
                        mk_evidence PAIR_EQ)
                   | _ => raise Refine)
           | _ => raise Refine)

    val FunEq : tactic =
      named "FunEq" (fn (G, P) =>
        case out P of
             CAN_EQ $ #[fun1, fun2, univ] =>
               (case (out fun1, out fun1, out univ) of
                    (FUN $ #[A,xB], FUN $ #[A',yB'], UNIV $ #[]) =>
                      let
                        val (x, Bx) = unbind xB
                        val B'x = subst1 yB' (`` x)
                        val Gx = Context.insert G x A
                      in
                        ([(G, EQ $$ #[A,A',univ]), (Gx, EQ $$ #[Bx,B'x,univ])],
                         fn [D, E] => FUN_EQ %$$ #[D, x %\\ E]
                          | _ => raise Refine)
                      end
                  | _ => raise Refine)
           | _ => raise Refine)

    val FunIntro : tactic =
      named "FunIntro" (fn (G, P) =>
        case out P of
             FUN $ #[P1, xP2] =>
               let
                 val (x, P2) = unbind xP2
                 val Gx = Context.insert G x P1
               in
                 ([(Gx, P2), (G, MEM $$ #[P1, UNIV $$ #[]])],
                  fn [D,E] => FUN_INTRO %$$ #[x %\\ D, E]
                    | _ => raise Refine)
               end
           | _ => raise Refine)

    val LamEq : tactic =
      named "LamEq" (fn (G, P) =>
        case out P of
             CAN_EQ $ #[lam, lam', func] =>
               (case (out lam, out lam', out func) of
                     (LAM $ #[zE], LAM $ #[z'E'], FUN $ #[A,xB]) =>
                     let
                       val (z, E) = unbind zE
                       val E'z = subst1 z'E' (`` z)
                       val Bz = subst1 xB (`` z)
                       val Gz = Context.insert G z A
                     in
                       ([(Gz, EQ $$ #[E, E'z, Bz]), (G, MEM $$ #[A, UNIV $$ #[]])],
                        fn [D, E] => LAM_EQ %$$ #[z %\\ D, E]
                           | _ => raise Refine)
                     end
                   | _ => raise Refine)
           | _ => raise Refine)

    val MemIntro : tactic =
      named "MemIntro" (fn (G, P) =>
      case out P of
           MEM $ #[M, A] =>
             ([(G, EQ $$ #[M, M, A])], mk_evidence MEM_INTRO)
         | _ => raise Refine)

    val EqIntro : tactic =
      named "EqIntro" (fn (G, P) =>
        case out P of
             EQ $ #[M, N, A] =>
               let
                 val M0 = Whnf.whnf M
                 val N0 = Whnf.whnf N
                 val A0 = Whnf.whnf A
               in
                 ([(G, CAN_EQ $$ #[M0, N0, A0])], mk_evidence EQ_INTRO)
               end
           | _ => raise Refine)

    fun Witness M : tactic =
      named "Witness" (fn (G, P) =>
        ([(G, MEM $$ #[M, P])], mk_evidence (WITNESS M)))

    val HypEq : tactic =
      named "HypEq" (fn (G, P) =>
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

    val ProdIntro : tactic =
      named "ProdIntro" (fn (G, P) =>
        case out P of
             PROD $ #[P1, P2] =>
               ([(G, P1), (G, P2)], mk_evidence PROD_INTRO)
           | _ => raise Refine)

    val ProdEq : tactic =
      named "ProdEq" (fn (G, P) =>
        case out P of
             CAN_EQ $ #[prod1, prod2, univ] =>
               (case (out prod1, out prod2, out univ) of
                    (PROD $ #[A,B], PROD $ #[A',B'], UNIV $ #[]) =>
                      ([(G, EQ $$ #[A,A',univ]), (G, EQ $$ #[B,B',univ])],
                       mk_evidence PROD_EQ)
                  | _ => raise Refine)
           | _ => raise Refine)

    fun Hypothesis x : tactic =
      named "Hypothesis" (fn (G, P) =>
        case Context.lookup G x of
              SOME P' =>
                if Syn.eq (P, P')
                then ([], fn _ => %`` x)
                else raise Refine
            | NONE => raise Refine)

    val Assumption : tactic =
      named "Assumption" (fn (G, P) =>
        case Context.search G (fn x => Syn.eq (P, x)) of
             SOME (x, _) => ([], fn _ => %`` x)
           | NONE => raise Refine)
  end

  structure DerivedTactics =
  struct
    open CoreTactics InferenceRules
    infix ORELSE ORELSE_LAZY THEN

    local
      val CanEqAuto = AxEq ORELSE PairEq ORELSE LamEq ORELSE UnitEq ORELSE ProdEq ORELSE VoidEq
      val EqAuto = (EqIntro THEN CanEqAuto) ORELSE HypEq
      val intro_rules =
        MemIntro ORELSE
          EqAuto ORELSE
            Assumption ORELSE
              ProdIntro ORELSE
                FunIntro ORELSE
                  UnitIntro
    in
      val Auto = REPEAT intro_rules
    end
  end
end

