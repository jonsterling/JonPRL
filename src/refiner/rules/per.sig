signature PER_RULES =
sig
  type tactic
  type hyp
  type name

  (* H >> per(a,b.R1) = per(c,d.R2) ∈ U{k}
   *   H, x : Base, y : Base >> R1[a\x,b\y] ∈ U{k}
   *   H, x : Base, y : Base >> R2[c\x,d\y] ∈ U{k}
   *   H, x : Base, y : Base, z : R1[a\x,b\y] >> R2[c\x,d\y]
   *   H, x : Base, y : Base, z : R2[c\x,d\y] >> R1[a\x,b\y]
   *   H, x : Base, y : Base, z : R1[a\x,b\y] >> R1[a\y,b\x]
   *   H, x : Base, y : Base, z : Base, u : R1[a\x,b\y], v : R1[a\y,b\z] >> R1[a\x,b\z]
   *)
  val Eq    : (name * name * name * name * name) option -> tactic

  (* H >> M = N ∈ per(a,b.R)
   *   H >> per(a,b.R) ∈ U{k}
   *   H >> R[a\M,b\N]
   *   H >> M ∈ Base
   *   H >> N ∈ Base
   *)
  val MemEq : Level.t option -> tactic

  (* H, z : M = N ∈ per(a,b.R), J >> P
   *   H, z : M = N ∈ per(a,b.R), [y : R[a\M,b\N]], J >> P
   *   H, z : M = N ∈ per(a,b.R), J >> R[a\M,b\N] ∈ U{k}
   *)
  val Elim  : hyp * name option * Level.t option -> tactic

end
