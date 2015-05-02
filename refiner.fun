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
    val UnitIntro : tactic
    val ProdIntro : tactic
    val ImpIntro : Context.name -> tactic
    val MemIntro : tactic
    val EqIntro : tactic
    val Witness : Syn.t -> tactic
    val VoidElim : tactic

    val AxIntro : tactic
    val PairIntro : tactic
    val LamIntro : tactic

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
      = UNIT_INTRO
      | PROD_INTRO
      | IMP_INTRO
      | AX_INTRO
      | PAIR_INTRO
      | LAM_INTRO
      | MEM_INTRO
      | EQ_INTRO
      | WITNESS of Syn.t
      | HYP_EQ
      | VOID_ELIM

    fun eq UNIT_INTRO UNIT_INTRO = true
      | eq PROD_INTRO PROD_INTRO = true
      | eq IMP_INTRO IMP_INTRO = true
      | eq AX_INTRO AX_INTRO = true
      | eq PAIR_INTRO PAIR_INTRO = true
      | eq LAM_INTRO LAM_INTRO = true
      | eq MEM_INTRO MEM_INTRO = true
      | eq EQ_INTRO EQ_INTRO = true
      | eq (WITNESS m) (WITNESS n) = Syn.eq (m, n)
      | eq HYP_EQ HYP_EQ = true
      | eq VOID_ELIM VOID_ELIM = true
      | eq _ _ = false

    fun arity UNIT_INTRO = #[]
      | arity PROD_INTRO = #[0,0]
      | arity IMP_INTRO = #[1]
      | arity AX_INTRO = #[]
      | arity PAIR_INTRO = #[0,0]
      | arity LAM_INTRO = #[1]
      | arity MEM_INTRO = #[0]
      | arity EQ_INTRO = #[0]
      | arity (WITNESS _) = #[0]
      | arity HYP_EQ = #[0]
      | arity VOID_ELIM = #[0]

    fun to_string UNIT_INTRO = "unit-I"
      | to_string PROD_INTRO = "prod-I"
      | to_string IMP_INTRO = "imp-I"
      | to_string AX_INTRO = "ax-I"
      | to_string PAIR_INTRO = "pair-I"
      | to_string LAM_INTRO = "lam-I"
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
         | IMP_INTRO $ #[xE] => Syn.$$ (LAM, #[extract xE])
         | AX_INTRO $ _ => Syn.$$ (AX, #[])
         | PAIR_INTRO $ _ => Syn.$$ (AX, #[])
         | LAM_INTRO $ _ => Syn.$$ (AX, #[])
         | MEM_INTRO $ _ => Syn.$$ (AX, #[])
         | VOID_ELIM $ _ => Syn.$$ (AX, #[])
         | WITNESS m $ _ => m
         | ` x => Syn.`` x
         | x \ E => Syn.\\ (x, extract E)
         | _ => raise MalformedEvidence ev
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
    fun fail name goal =
      raise Fail (name ^ "| " ^ print_goal goal)

    val UnitIntro : tactic = fn (G, P) =>
      case out P of
           UNIT $ _ => ([], fn args => UNIT_INTRO %$$ Vector.fromList args)
         | _ => fail "UnitIntro" (G, P)

    val VoidElim : tactic = fn (G, P) =>
      ([(G, VOID $$ #[])], fn args => VOID_ELIM %$$ Vector.fromList args)

    val AxIntro : tactic = fn (G, P) =>
      case out P of
           CAN_EQ $ #[ax, ax', unit] =>
             (case (out ax, out ax', out unit) of
                  (AX $ #[], AX $ #[], UNIT $ #[]) =>
                    ([], fn args => AX_INTRO %$$ Vector.fromList args)
                | _ => fail "AxIntro" (G, P))
         | _ => fail "AxIntro" (G, P)

    val PairIntro : tactic = fn (G, P) =>
      case out P of
           CAN_EQ $ #[pair, pair', prod] =>
             (case (out pair, out pair', out prod) of
                   (PAIR $ #[M,N], PAIR $ #[M', N'], PROD $ #[A,B]) =>
                     ([(G, EQ $$ #[M,M',A]), (G, EQ $$ #[N,N',B])],
                      fn args => PAIR_INTRO %$$ Vector.fromList args)
                 | _ => fail "PairIntro" (G, P))
         | _ => fail "PairIntro" (G, P)

    val LamIntro : tactic = fn (G, P) =>
      case out P of
           CAN_EQ $ #[lam, lam', imp] =>
             (case (out lam, out lam', out imp) of
                   (LAM $ #[zE], LAM $ #[z'E'], IMP $ #[A,B]) =>
                   let
                     val (z, E) = unbind zE
                     val E'z = subst1 z'E' (`` z)
                   in
                     ([(Context.insert G z A, EQ $$ #[E, E'z, B])],
                      fn [D] => LAM_INTRO %$$ #[z %\\ D]
                         | _ => fail "ImpIntro" (G, P))
                   end
                 | _ => fail "LamIntro" (G, P))
         | _ => fail "LamIntro" (G, P)

    val MemIntro : tactic = fn (G, P) =>
      case out P of
           MEM $ #[M, A] =>
             ([(G, EQ $$ #[M, M, A])],
              fn args => MEM_INTRO %$$ Vector.fromList args)
         | _ => fail "MemIntro" (G, P)

    val EqIntro : tactic = fn (G, P) =>
      case out P of
           EQ $ #[M, N, A] =>
             let
               val M0 = Whnf.whnf M
               val N0 = Whnf.whnf N
               val A0 = Whnf.whnf A
             in
               ([(G, CAN_EQ $$ #[M0, N0, A0])],
                fn args => EQ_INTRO %$$ Vector.fromList args)
             end
         | _ => fail "EqIntro" (G, P)

    fun Witness M : tactic = fn (G, P) =>
      ([(G, MEM $$ #[M, P])],
       fn [D] => WITNESS M %$$ #[D]
         | _ => fail "Witness" (G,P))

    val HypEq : tactic = fn (G, P) =>
      case out P of
           EQ $ #[M,M',A] =>
           (case (Syn.eq (M, M'), out M) of
                 (true, ` x) =>
                   (case Context.lookup G x of
                         SOME Q =>
                           if Syn.eq (A, Q)
                           then ([], fn _ => HYP_EQ %$$ #[%`` x])
                           else fail "HypEq" (G, P)
                       | NONE => fail "HypEq" (G, P))
               | _ => fail "HypEq" (G, P))
         | _ => fail "HypEq" (G, P)

    val ProdIntro : tactic = fn (G, P) =>
      case out P of
           PROD $ #[P1, P2] =>
             ([(G, P1), (G, P2)],
              fn args => PROD_INTRO %$$ Vector.fromList args)
         | _ => fail "ProdIntro" (G, P)

    fun ImpIntro x : tactic = fn (G, P) =>
      case out P of
           IMP $ #[P1, P2] =>
             ([(Context.insert G x P1, P2)],
              fn [D] => IMP_INTRO %$$ #[x %\\ D]
                | _ => fail "ImpIntro" (G, P))
         | _ => fail "ImpIntro" (G, P)

    fun Hypothesis x : tactic = fn (G, P) =>
      (case Context.lookup G x of
            SOME P' =>
              if Syn.eq (P, P')
              then ([], fn _ => %`` x)
              else fail "Hypothesis" (G, P)
          | NONE => fail "Hypothesis" (G, P))

    val Assumption : tactic = fn (G, P) =>
      (case Context.search G (fn x => Syn.eq (P, x)) of
           SOME (x, _) => ([], fn _ => %`` x)
         | NONE => fail "Assumption" (G, P))
  end

  structure DerivedTactics =
  struct
    open CoreTactics InferenceRules
    infix ORELSE ORELSE_LAZY THEN

    val CanEqAuto = AxIntro ORELSE PairIntro ORELSE LamIntro
    val EqAuto = (EqIntro THEN CanEqAuto) ORELSE HypEq

    local
      val intro_rules =
        MemIntro ORELSE
          EqAuto ORELSE
            Assumption ORELSE
              ProdIntro ORELSE_LAZY (fn () =>
                ImpIntro (Variable.new()) ORELSE
                  UnitIntro )
    in
      val Auto = REPEAT intro_rules
    end
  end
end

