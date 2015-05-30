signature ABT_UTIL =
sig
  include ABT

  val `` : Variable.t -> t
  val \\ : Variable.t * t -> t
  val $$ : Operator.t * t vector -> t

  val free_variables : t -> Variable.t list
  val has_free : t * Variable.t -> bool

  val subst : t -> Variable.t -> t -> t
  val to_string : t -> string
  val to_string_open : (t -> string) -> t -> string

  val unbind : t -> Variable.t * t

  val subst1 : (* binding *) t -> t -> t
  val // : (* binding *) t * t -> t

  exception ExpectedBinding of t

end
