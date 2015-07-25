signature SMALL_STEP =
sig
  type syn

  datatype t = STEP of syn | CANON | NEUTRAL
  exception Stuck of syn

  val step : syn -> t
end

signature SMALL_STEP_UTIL =
sig
  include SMALL_STEP

  type petrol = int

  (* Evaluate a term with a bit of petrol, returning the result and the amount
   * of petrol expended. *)
  val steps : syn * petrol option -> syn * petrol
end
