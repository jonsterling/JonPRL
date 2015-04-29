functor EVIDENCE
  (structure Syn : ABTUTIL where Operator = Judgements) :>
sig
  datatype ev
    = triv
    | canon of Syn.t
    | match of (Syn.t -> ev)
    | generalize of (Syn.Variable.t -> ev)

  val chk : Syn.t -> ev -> unit
end =
struct
  datatype ev
    = triv
    | canon of Syn.t
    | match of (Syn.t -> ev)
    | generalize of (Syn.Variable.t -> ev)

  exception Hole

  open Syn
  infix $
  infix $$

  fun chk j ev =
    case out j of
         j' => raise Hole
end

