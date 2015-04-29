signature ABTUTIL =
sig

  include ABT

  val `` : Variable.t -> t
  val \\ : Variable.t * t -> t
  val $$ : Operator.t * t vector -> t

  val subst : t -> Variable.t -> t -> t
  val to_string : t -> string

  val unbind : t -> Variable.t * t

  val subst1 : (* binding *) t -> t -> t

  exception ExpectedBinding of t

end
