signature PER_RULES =
sig
  type tactic
  type hyp
  type name

  (* H >> per(R1) = per(R2) ∈ U{k}
   *   H, x : Base, y : Base >> R1 x y ∈ U{k}
   *   H, x : Base, y : Base >> R2 x y ∈ U{k}
   *   H, x : Base, y : Base, z : R1 x y >> R2 x y
   *   H, x : Base, y : Base, z : R2 x y >> R1 x y
   *   H, x : Base, y : Base, z : R1 x y >> R1 y x
   *   H, x : Base, y : Base, z : Base, u : R1 x y, v : R1 y z >> R1 x z
   *)
  val Eq    : (name * name * name * name * name) option -> tactic

  (* H >> M = N ∈ per(R)
   *   H >> per(R) ∈ U{k}
   *   H >> R M N
   *   H >> M ∈ Base
   *   H >> N ∈ Base
   *)
  val MemEq : Level.t option -> tactic

  (* H, z : M = N ∈ per(R), J >> P
   *   H, z : M = N ∈ per(R), [y : R M N], J >> P
   *   H, z : M = N ∈ per(R), J >> R M N ∈ U{k}
   *)
  val Elim  : hyp * name option * Level.t option -> tactic

end
