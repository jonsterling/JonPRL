functor Whnf (Syn : ABTUTIL where Operator = Lang) :
sig
  val whnf : Syn.t -> Syn.t
  exception WhnfStuck
end =
struct
  exception WhnfStuck

  open Lang Syn
  infix $ $$

  fun whnf x =
    case out x of
         SPREAD $ #[M, xyN] =>
           (case out (whnf M) of
                PAIR $ #[M1, M2] =>
                  let
                    val (x,yN) = unbind xyN
                    val (y, N) = unbind yN
                    val N' = subst M1 x (subst M2 y N)
                  in
                    whnf N'
                  end
              | _ => raise WhnfStuck)
       | AP $ #[M,N] =>
           (case out (whnf M) of
                 LAM $ #[xE] => whnf (subst1 xE N)
               | _ => raise WhnfStuck)
       | MATCH_UNIT $ #[M,N] =>
           (case out (whnf M) of
                 AX $ #[] => whnf N
               | _ => raise WhnfStuck)
       | _ => x


end
