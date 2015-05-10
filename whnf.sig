signature WHNF =
sig
  type term

  exception Stuck of term
  val whnf : term -> term
end

