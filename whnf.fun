functor Whnf (Syn : ABTUTIL where Operator = Lang) :
sig
  val whnf : Syn.t -> Syn.t
end =
struct
  open Lang Syn
  infix $ $$

  fun whnf x =
    case out x of
         FST $ #[M] =>
           (case out (whnf M) of
                PAIR $ #[M1, M2] => whnf M1
              | _ => x)
       | SND $ #[M] =>
           (case out (whnf M) of
                 PAIR $ #[M1, M2] => whnf M2
               | _ => x)
       | _ => x


end
