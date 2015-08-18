signature IMAGE_RULES =
sig
  type tactic
  type hyp
  type name

  (* H >> image(A1;f1) = image(A2;f2) ∈ U{k}
   *   H >> f1 = f2 ∈ Base
   *   H >> A1 = A2 ∈ U{k}
   *)
  val Eq    : tactic

  (* H >> f a1 = f a2 ∈ image(A;f)
   *   H >> a1 = a2 in A
   *   H >> f = f ∈ Base
   *)
  val MemEq : tactic

  (* H, z : image(A;f), J >> P
   *   H, z : image(A;f), [w : A], J[z\f w] >> P[z\f w]
   *)
  val Elim  : hyp * name option -> tactic

  (* H, x : t2 = f t1 ∈ image(A;f), J >> t2 = f t1 ∈ T
   *   H >> f ∈ Base
   *   H >> t1 ∈ A
   *   H >> f t1 ∈ T
   *   H, a : Base, b : Base, y : f a ∈ T, z : a = b ∈ A >> f a = f b ∈ T
   *)
  val EqInd : hyp * (name * name * name * name) option -> tactic
end
