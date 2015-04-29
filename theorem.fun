structure ListUtil :
sig
  val split : int -> 'a list -> 'a list * 'a list
  val multisplit : int list -> 'a list -> 'a list list
end =
struct
  exception Hole

  local
    fun go 0 (xs, ys) = (xs, ys)
      | go n (xs, []) = ([], xs)
      | go n (xs, y::ys) = go (n - 1) (xs @ [y], ys)
  in
    fun split i xs = go i ([], xs)
  end

  local
    fun go [] xs r = r @ [xs]
      | go (n::ns) xs r =
        let
          val (ys,zs) = split n xs
        in
          go ns zs (r @ [ys])
        end
  in
    fun multisplit ns xs = go ns xs []
  end
end

functor Theorem (Syn : ABTUTIL where Operator = Lang and Variable = Variable) :
sig
  type ctx = Syn.t Context.context
  type goal = ctx * Syn.t

  structure Evidence : ABTUTIL
  exception MalformedEvidence of Evidence.t
  val extract : Evidence.t -> Syn.t

  type validation = Evidence.t list -> Evidence.t
  type tactic = goal -> (goal list * validation)

  val THEN : tactic * tactic -> tactic
  val ORELSE : tactic * tactic -> tactic

  val UnitIntro : tactic
  val ProdIntro : tactic
  val ImpIntro : Context.name -> tactic
  val AxIntro : tactic
  val PairIntro : tactic
  val LamIntro : Context.name -> tactic
  val MemIntro : tactic
  val CanMemAuto : tactic
  val MemAuto : tactic

  val Assumption : tactic
  val Hypothesis : Context.name -> tactic
end =
struct
  type ctx = Syn.t Context.context
  type goal = ctx * Syn.t

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

    fun eq (x : t) y = x = y

    fun arity UNIT_INTRO = #[]
      | arity PROD_INTRO = #[0,0]
      | arity IMP_INTRO = #[1]
      | arity AX_INTRO = #[]
      | arity PAIR_INTRO = #[0,0]
      | arity LAM_INTRO = #[1]
      | arity MEM_INTRO = #[0]

    fun to_string UNIT_INTRO = "unit-I"
      | to_string PROD_INTRO = "prod-I"
      | to_string IMP_INTRO = "imp-I"
      | to_string AX_INTRO = "ax-I"
      | to_string PAIR_INTRO = "pair-I"
      | to_string LAM_INTRO = "lam-I"
      | to_string MEM_INTRO = "∈*-I"
  end

  structure Evidence = AbtUtil(Abt(structure Operator=EOp and Variable = Variable))
  structure E = Evidence

  type validation = Evidence.t list -> Evidence.t
  type tactic = goal -> (goal list * validation)

  exception Hole

  exception MalformedEvidence of E.t

  local
    open E EOp Lang
    infix $
  in
    fun extract (ev : E.t) : Syn.t =
      case out ev of
           UNIT_INTRO $ #[] => Syn.$$ (AX, #[])
         | PROD_INTRO $ #[D,E] => Syn.$$ (PAIR, #[extract D, extract E])
         | IMP_INTRO $ #[xE] =>
             let
               val (x, E) = unbind xE
             in
               Syn.$$ (LAM, #[Syn.\\ (x, extract E)])
             end
         | AX_INTRO $ _ => Syn.$$ (AX, #[])
         | PAIR_INTRO $ _ => Syn.$$ (AX, #[])
         | LAM_INTRO $ _ => Syn.$$ (AX, #[])
         | MEM_INTRO $ _ => Syn.$$ (AX, #[])
         | ` x => Syn.`` x
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

  val UnitIntro : tactic = fn (G, P) =>
    case out P of
         UNIT $ _ => ([], fn args => UNIT_INTRO %$$ Vector.fromList args)
       | _ => raise Fail "UnitIntro"

  val AxIntro : tactic = fn (G, P) =>
    case out P of
         CAN_MEM $ #[ax, unit] =>
           (case (out ax, out unit) of
                (AX $ #[], UNIT $ #[]) =>
                  ([], fn args => AX_INTRO %$$ Vector.fromList args)
              | _ => raise Fail "AxIntro")
       | _ => raise Fail "AxIntro"

  val PairIntro : tactic = fn (G, P) =>
    case out P of
         CAN_MEM $ #[pair, prod] =>
           (case (out pair, out prod) of
                 (PAIR $ #[M,N], PROD $ #[A,B]) =>
                   ([(G, MEM $$ #[M,A]), (G, MEM $$ #[N,B])],
                    fn args => PAIR_INTRO %$$ Vector.fromList args)
               | _ => raise Fail "PairIntro")
       | _ => raise Fail "PairIntro"

  fun LamIntro d : tactic = fn (G, P) =>
    case out P of
         CAN_MEM $ #[lam, imp] =>
           (case (out lam, out imp) of
                 (LAM $ #[zE], IMP $ #[A,B]) =>
                 let
                   val (z, E) = unbind zE
                   val G' = Context.insert G d (MEM $$ #[``z, A])
                 in
                   ([(G', MEM $$ #[E, B])],
                    fn [D] => LAM_INTRO %$$ #[d %\\ D]
                       | _ => raise Fail "ImpIntro")
                 end
               | _ => raise Fail "LamIntro")
       | _ => raise Fail "LamIntro"

  val MemIntro : tactic = fn (G, P) =>
    case out P of
         MEM $ #[M, A] =>
         let
           val M0 = Whnf.whnf M
           val A0 = Whnf.whnf A
         in
           ([(G, CAN_MEM $$ #[M0, A0])], fn args => MEM_INTRO %$$ Vector.fromList args)
         end
       | _ => raise Fail "MemIntro"

  val ProdIntro : tactic = fn (G, P) =>
    case out P of
         PROD $ #[P1, P2] =>
           ([(G, P1), (G, P2)],
            fn args => PROD_INTRO %$$ Vector.fromList args)
       | _ => raise Fail "ProdIntro"

  fun ImpIntro x : tactic = fn (G, P) =>
    case out P of
         IMP $ #[P1, P2] =>
           ([(Context.insert G x P1, P2)],
            fn [D] => IMP_INTRO %$$ #[x %\\ D]
              | _ => raise Fail "ImpIntro")
       | _ => raise Fail "ImpIntro"

  fun Hypothesis x : tactic = fn (G, P) =>
    (case Context.lookup G x of
          SOME P' =>
            if Syn.eq (P, P')
            then ([], fn _ => %`` x)
            else raise Fail "Hypothesis does not match"
        | NONE => raise Fail "No such hypothesis")

  val Assumption : tactic = fn (G, P) =>
    (case Context.search G (fn x => Syn.eq (P, x)) of
         SOME (x, _) => ([], fn _ => %`` x)
       | NONE => raise Fail "No matching assumption")

  fun THEN (tac1 : tactic, tac2 : tactic) (g : goal) =
    let
      val (subgoals1, validation1) = tac1 g
      val (subgoals2, validations2) = ListPair.unzip (List.map tac2 subgoals1)
    in
      (List.foldl (op @) [] subgoals2,
       fn Ds =>
         let
           val lengths = List.map List.length subgoals2
           val derivations : Evidence.t list list = ListUtil.multisplit lengths Ds
         in
           validation1 (ListPair.map (fn (v, d) => v d) (validations2, derivations))
         end)
    end

  fun ORELSE (tac1 : tactic, tac2 : tactic) : tactic = fn g =>
    tac1 g handle _ => tac2 g

  infix ORELSE
  infix THEN

  val CanMemAuto = AxIntro ORELSE PairIntro ORELSE (LamIntro (Variable.new ()))
  val MemAuto = MemIntro THEN CanMemAuto
end

structure Test =
struct

  structure Syn = AbtUtil(Abt(structure Operator = Lang and Variable = Variable))
  structure Theorem = Theorem(Syn)
  structure Ctx = Context
  open Lang
  open Syn
  infix $$ \\

  open Theorem
  infix THEN ORELSE

  exception RemainingSubgoals of goal list

  fun check P (tac : tactic) =
  let
    val (subgoals, validate) = tac (Context.empty, P)
    val result = if null subgoals then validate [] else raise RemainingSubgoals subgoals
  in
    (print ("Theorem: " ^ Syn.to_string P ^ "\n");
     print ("Evidence: " ^ Evidence.to_string result ^ "\n");
     print ("Extract: " ^ Syn.to_string (extract result) ^ "\n\n"))
  end

  val ax = AX $$ #[]
  val unit = UNIT $$ #[]

  fun & (a, b) = PROD $$ #[a,b]
  infix &

  fun pair m n = PAIR $$ #[m,n]
  fun fst m = FST $$ #[m]
  fun lam e = LAM $$ #[e]

  fun ~> (a, b) = IMP $$ #[a,b]
  infix ~>

  fun can_mem (m, a) = CAN_MEM $$ #[m,a]
  infix can_mem

  fun mem (m, a) = MEM $$ #[m,a]
  infix mem

  val _ =
      check
        (unit & (unit & unit))
        (ProdIntro THEN
          (UnitIntro ORELSE
            (ProdIntro THEN UnitIntro)))

  val x = Variable.named "x"
  val _ =
     check
       (unit ~> (unit & unit))
       (ImpIntro x THEN (ProdIntro THEN Assumption))

  val _ =
      check
        (fst (pair ax ax) mem unit)
        (MemAuto THEN MemAuto)

  val _ =
      check
        (lam (x \\ `` x) mem (unit ~> unit))
        (MemAuto THEN Assumption)
end
