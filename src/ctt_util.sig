signature CTT_UTIL =
sig
  include CTT
  val Auto : Lcf.tactic

  type intro_args =
    {term : Syntax.t option,
     freshVariable : name option,
     level : Level.t option}

  type elim_args =
    {target : int,
     names : name list,
     term : term option}

  type eq_cd_args =
    {names : name list,
     level : Level.t option,
     terms : term list}

  val Intro : intro_args -> Lcf.tactic
  val Elim : elim_args -> Lcf.tactic
  val EqCD : eq_cd_args -> Lcf.tactic

end
